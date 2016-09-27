{- |
    Module      :  $Header$
    Description :  Checks precedences of infix operators
    Copyright   :  (c) 2001 - 2004 Wolfgang Lux
                                   Martin Engelke
                                   Björn Peemöller
                       2015        Jan Tikovsky
                       2016        Finn Teegen
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The parser does not know the relative precedences of infix operators
   and therefore parses them as if they all associate to the right and
   have the same precedence. After performing the definition checks,
   the compiler is going to process the infix applications in the module
   and rearrange infix applications according to the relative precedences
   of the operators involved.
-}
{-# LANGUAGE CPP #-}
module Checks.PrecCheck (precCheck) where

#if __GLASGOW_HASKELL__ < 710
import           Control.Applicative      ((<$>), (<*>))
#endif
import           Control.Monad            (unless, when)
import qualified Control.Monad.State as S (State, runState, gets, modify)
import           Data.List                (partition)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Pretty
import Curry.Syntax

import Base.Expr
import Base.Messages (Message, posMessage, internalError)
import Base.Utils    (findMultiples)

import Env.OpPrec (OpPrecEnv, OpPrec (..), PrecInfo (..), defaultP, bindP
  , mkPrec, qualLookupP)

precCheck :: ModuleIdent -> OpPrecEnv -> [Decl a] -> ([Decl a], OpPrecEnv, [Message])
precCheck m pEnv decls = runPCM (checkDecls decls) initState
 where initState = PCState m pEnv []

data PCState = PCState
  { moduleIdent :: ModuleIdent
  , precEnv     :: OpPrecEnv
  , errors      :: [Message]
  }

type PCM = S.State PCState -- the Prec Check Monad

runPCM :: PCM a -> PCState -> (a, OpPrecEnv, [Message])
runPCM kcm s = let (a, s') = S.runState kcm s
               in  (a, precEnv s', reverse $ errors s')

getModuleIdent :: PCM ModuleIdent
getModuleIdent = S.gets moduleIdent

getPrecEnv :: PCM OpPrecEnv
getPrecEnv = S.gets precEnv

modifyPrecEnv :: (OpPrecEnv -> OpPrecEnv) -> PCM ()
modifyPrecEnv f = S.modify $ \ s -> s { precEnv = f $ precEnv s }

withLocalPrecEnv :: PCM a -> PCM a
withLocalPrecEnv act = do
  oldEnv <- getPrecEnv
  res <- act
  modifyPrecEnv $ const oldEnv
  return res

report :: Message -> PCM ()
report err = S.modify (\ s -> s { errors = err : errors s })

-- For each declaration group, including the module-level, the compiler
-- first checks that its fixity declarations contain no duplicates and
-- that there is a corresponding value or constructor declaration in that
-- group. The fixity declarations are then used for extending the
-- imported precedence environment.

bindPrecs :: [Decl a] -> PCM ()
bindPrecs ds0 = case findMultiples opFixDecls of
  [] -> case filter (`notElem` bvs) opFixDecls of
    []  -> do
      m <- getModuleIdent
      modifyPrecEnv $ \env -> foldr (bindPrec m) env fixDs
    ops -> mapM_ (report . errUndefinedOperator) ops
  opss -> mapM_ (report . errMultiplePrecedence) opss
  where
    ds                = concatMap decls ds0
    (fixDs, nonFixDs) = partition isInfixDecl ds
    opFixDecls        = [ op | InfixDecl _ _ _ ops <- fixDs, op <- ops ]
    -- Unrenaming is necessary here, because operators within class
    -- declarations have been renamed during syntax checking.
    bvs               = map unRenameIdent $ concatMap boundValues nonFixDs
    decls (ClassDecl _ _ _ _ innerDs) = innerDs
    decls d                           = [d]

bindPrec :: ModuleIdent -> Decl a -> OpPrecEnv -> OpPrecEnv
bindPrec m (InfixDecl _ fix mprec ops) pEnv
  | p == defaultP = pEnv
  | otherwise     = foldr (flip (bindP m) p) pEnv ops
  where p = OpPrec fix (mkPrec mprec)
bindPrec _ _                           pEnv = pEnv

boundValues :: Decl a -> [Ident]
boundValues (DataDecl     _ _ _ cs _) = [ v | c <- cs
                                            , v <- constrId c : recordLabels c]
boundValues (NewtypeDecl  _ _ _ nc _) = nconstrId nc : nrecordLabels nc
boundValues (TypeSig          _ fs _) = fs
boundValues (FunctionDecl    _ _ f _) = [f]
boundValues (ForeignDecl _ _ _ _ f _) = [f]
boundValues (ExternalDecl       _ vs) = bv vs
boundValues (PatternDecl       _ t _) = bv t
boundValues (FreeDecl           _ vs) = bv vs
boundValues _                         = []

-- With the help of the precedence environment, the compiler checks all
-- infix applications and sections in the program. This pass will modify
-- the parse tree such that for a nested infix application the operator
-- with the lowest precedence becomes the root and that two adjacent
-- operators with the same precedence will not have conflicting
-- associativities. Note that the top-level precedence environment has to
-- be returned because it is needed for constructing the module's
-- interface.

checkDecls :: [Decl a] -> PCM [Decl a]
checkDecls decls = bindPrecs decls >> mapM checkDecl decls

checkDecl :: Decl a -> PCM (Decl a)
checkDecl (FunctionDecl p a f           eqs) =
  FunctionDecl p a f <$> mapM checkEquation eqs
checkDecl (PatternDecl  p t             rhs) =
  PatternDecl p <$> checkPattern t <*> checkRhs rhs
checkDecl (ClassDecl    p cx cls    tv   ds) =
  ClassDecl p cx cls tv <$> mapM checkDecl ds
checkDecl (InstanceDecl p cx qcls   inst ds) =
  InstanceDecl p cx qcls inst <$> mapM checkDecl ds
checkDecl d                                  = return d

checkEquation :: Equation a -> PCM (Equation a)
checkEquation (Equation p lhs rhs) =
  Equation p <$> checkLhs lhs <*> checkRhs rhs

checkLhs :: Lhs a -> PCM (Lhs a)
checkLhs (FunLhs    f ts) = FunLhs f <$> mapM checkPattern ts
checkLhs (OpLhs t1 op t2) =
  flip OpLhs op <$> (checkPattern t1 >>= checkOpL op)
                <*> (checkPattern t2 >>= checkOpR op)
checkLhs (ApLhs   lhs ts) =
  ApLhs <$> checkLhs lhs <*> mapM checkPattern ts

checkPattern :: Pattern a -> PCM (Pattern a)
checkPattern l@(LiteralPattern        _ _) = return l
checkPattern n@(NegativePattern     _ _ _) = return n
checkPattern v@(VariablePattern       _ _) = return v
checkPattern (ConstructorPattern   a c ts) =
  ConstructorPattern a c <$> mapM checkPattern ts
checkPattern (InfixPattern     a t1 op t2) = do
  t1' <- checkPattern t1
  t2' <- checkPattern t2
  fixPrecT (InfixPattern a) t1' op t2'
checkPattern (ParenPattern              t) =
  ParenPattern <$> checkPattern t
checkPattern (TuplePattern           p ts) =
  TuplePattern p <$> mapM checkPattern ts
checkPattern (ListPattern          a p ts) =
  ListPattern a p <$> mapM checkPattern ts
checkPattern (AsPattern               v t) =
  AsPattern v <$> checkPattern t
checkPattern (LazyPattern             p t) =
  LazyPattern p <$> checkPattern t
checkPattern (FunctionPattern      a f ts) =
  FunctionPattern a f <$> mapM checkPattern ts
checkPattern (InfixFuncPattern a t1 op t2) = do
  t1' <- checkPattern t1
  t2' <- checkPattern t2
  fixPrecT (InfixFuncPattern a) t1' op t2'
checkPattern (RecordPattern       a c fs) =
  RecordPattern a c <$> mapM (checkField checkPattern) fs

checkRhs :: Rhs a -> PCM (Rhs a)
checkRhs (SimpleRhs p e ds) = withLocalPrecEnv $
  flip (SimpleRhs p) <$> checkDecls ds <*> checkExpr e
checkRhs (GuardedRhs es ds) = withLocalPrecEnv $
  (flip GuardedRhs) <$> checkDecls ds <*> mapM checkCondExpr es

checkCondExpr :: CondExpr a -> PCM (CondExpr a)
checkCondExpr (CondExpr p g e) = CondExpr p <$> checkExpr g <*> checkExpr e

checkExpr :: Expression a -> PCM (Expression a)
checkExpr l@(Literal       _ _) = return l
checkExpr v@(Variable      _ _) = return v
checkExpr c@(Constructor   _ _) = return c
checkExpr (Paren             e) = Paren <$> checkExpr e
checkExpr (Typed          e ty) = flip Typed ty <$> checkExpr e
checkExpr (Record       a c fs) = Record a c <$> mapM (checkField checkExpr) fs
checkExpr (RecordUpdate   e fs) = RecordUpdate <$> (checkExpr e)
                                             <*> mapM (checkField checkExpr) fs
checkExpr (Tuple   p es) = Tuple p <$> mapM checkExpr es
checkExpr (List  a p es) = List a p <$> mapM checkExpr es
checkExpr (ListCompr p e qs) = withLocalPrecEnv $
  flip (ListCompr p) <$> mapM checkStmt qs <*> checkExpr e
checkExpr (EnumFrom              e) = EnumFrom <$> checkExpr e
checkExpr (EnumFromThen      e1 e2) =
  EnumFromThen <$> checkExpr e1 <*> checkExpr e2
checkExpr (EnumFromTo        e1 e2) =
  EnumFromTo <$> checkExpr e1 <*> checkExpr e2
checkExpr (EnumFromThenTo e1 e2 e3) =
  EnumFromThenTo <$> checkExpr e1 <*> checkExpr e2 <*> checkExpr e3
checkExpr (UnaryMinus          r e) = UnaryMinus r <$> checkExpr e
checkExpr (Apply e1 e2) =
  Apply <$> checkExpr e1 <*> checkExpr e2
checkExpr (InfixApply e1 op e2) = do
  e1' <- checkExpr e1
  e2' <- checkExpr e2
  fixPrec e1' op e2'
checkExpr (LeftSection      e op) = checkExpr e >>= checkLSection op
checkExpr (RightSection     op e) = checkExpr e >>= checkRSection op
checkExpr (Lambda         r ts e) =
  (Lambda r) <$> mapM checkPattern ts <*> checkExpr e
checkExpr (Let              ds e) = withLocalPrecEnv $
  Let <$> checkDecls ds <*> checkExpr e
checkExpr (Do              sts e) = withLocalPrecEnv $
  Do <$>  mapM checkStmt sts <*> checkExpr e
checkExpr (IfThenElse r e1 e2 e3) =
  IfThenElse r <$> checkExpr e1 <*> checkExpr e2 <*> checkExpr e3
checkExpr (Case      r ct e alts) =
  Case r ct <$> checkExpr e <*> mapM checkAlt alts

checkStmt :: Statement a -> PCM (Statement a)
checkStmt (StmtExpr   p e) = StmtExpr p <$> checkExpr e
checkStmt (StmtDecl    ds) = StmtDecl   <$> checkDecls ds
checkStmt (StmtBind p t e) = StmtBind p <$> checkPattern t <*> checkExpr e

checkAlt :: Alt a -> PCM (Alt a)
checkAlt (Alt p t rhs) = Alt p <$> checkPattern t <*> checkRhs rhs

checkField :: (a -> PCM a) -> Field a -> PCM (Field a)
checkField check (Field p l x) = Field p l <$> check x

-- The functions 'fixPrec', 'fixUPrec', and 'fixRPrec' check the relative
-- precedences of adjacent infix operators in nested infix applications
-- and unary negations. The expressions will be reordered such that the
-- infix operator with the lowest precedence becomes the root of the
-- expression. The functions rely on the fact that the parser constructs
-- infix applications in a right-associative fashion, i.e., the left argument
-- of an infix application will never be an infix application. In addition,
-- a unary negation will never have an infix application as its argument.

-- The function 'fixPrec' checks whether the left argument of an
-- infix application is a unary negation and eventually reorders the
-- expression if the precedence of the infix operator is higher than that
-- of the negation. This will be done with the help of the function
-- 'fixUPrec'. In any case, the function 'fixRPrec' is used for fixing the
-- precedence of the infix operator and that of its right argument.
-- Note that both arguments already have been checked before 'fixPrec'
-- is called.

fixPrec :: Expression a -> InfixOp a -> Expression a -> PCM (Expression a)
fixPrec (UnaryMinus ref e1) op e2 = do
  OpPrec fix pr <- getOpPrec op
  if pr < 6 || pr == 6 && fix == InfixL
    then fixRPrec (UnaryMinus ref e1) op e2
    else if pr > 6
      then fixUPrec ref e1 op e2
      else do
        report $ errAmbiguousParse "unary" (qualify minusId) (opName op)
        return $ InfixApply (UnaryMinus ref e1) op e2
fixPrec e1 op e2 = fixRPrec e1 op e2

fixUPrec :: SrcRef -> Expression a -> InfixOp a -> Expression a
         -> PCM (Expression a)
fixUPrec ref e1 op e2@(UnaryMinus _ _) = do
  report $ errAmbiguousParse "operator" (opName op) (qualify minusId)
  return $ UnaryMinus ref (InfixApply e1 op e2)
fixUPrec ref e1 op1 e'@(InfixApply e2 op2 e3) = do
  OpPrec fix2 pr2 <- getOpPrec op2
  if pr2 < 6 || pr2 == 6 && fix2 == InfixL
    then do
      left <- fixUPrec ref e1 op1 e2
      return $ InfixApply left op2 e3
    else if pr2 > 6
      then do
        op <- fixRPrec e1 op1 $ InfixApply e2 op2 e3
        return $ UnaryMinus ref op
      else do
        report $ errAmbiguousParse "unary" (qualify minusId) (opName op2)
        return $ InfixApply (UnaryMinus ref e1) op1 e'
fixUPrec ref e1 op e2 = return $ UnaryMinus ref (InfixApply e1 op e2)

fixRPrec :: Expression a -> InfixOp a -> Expression a -> PCM (Expression a)
fixRPrec e1 op (UnaryMinus ref e2) = do
  OpPrec _ pr <- getOpPrec op
  unless (pr < 6) $ report $ errAmbiguousParse "operator" (opName op) (qualify minusId)
  return $ InfixApply e1 op $ UnaryMinus ref e2
fixRPrec e1 op1 (InfixApply e2 op2 e3) = do
  OpPrec fix1 pr1 <- getOpPrec op1
  OpPrec fix2 pr2 <- getOpPrec op2
  if pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR
     then return $ InfixApply e1 op1 $ InfixApply e2 op2 e3
     else if pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL
       then do
          left <- fixPrec e1 op1 e2
          return $ InfixApply left op2 e3
       else do
         report $ errAmbiguousParse "operator" (opName op1) (opName op2)
         return $ InfixApply e1 op1 $ InfixApply e2 op2 e3
fixRPrec e1 op e2 = return $ InfixApply e1 op e2

-- The functions 'checkLSection' and 'checkRSection' are used for handling
-- the precedences inside left and right sections.
-- These functions only need to check that an infix operator occurring in
-- the section has either a higher precedence than the section operator
-- or both operators have the same precedence and are both left
-- associative for a left section and right associative for a right
-- section, respectively.

checkLSection :: InfixOp a -> Expression a -> PCM (Expression a)
checkLSection op e@(UnaryMinus _ _) = do
  OpPrec fix pr <- getOpPrec op
  unless (pr < 6 || pr == 6 && fix == InfixL) $
    report $ errAmbiguousParse "unary" (qualify minusId) (opName op)
  return $ LeftSection e op
checkLSection op1 e@(InfixApply _ op2 _) = do
  OpPrec fix1 pr1 <- getOpPrec op1
  OpPrec fix2 pr2 <- getOpPrec op2
  unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL) $
    report $ errAmbiguousParse "operator" (opName op1) (opName op2)
  return $ LeftSection e op1
checkLSection op e = return $ LeftSection e op

checkRSection :: InfixOp a -> Expression a -> PCM (Expression a)
checkRSection op e@(UnaryMinus _ _) = do
  OpPrec _ pr <- getOpPrec op
  unless (pr < 6) $ report $ errAmbiguousParse "unary" (qualify minusId) (opName op)
  return $ RightSection op e
checkRSection op1 e@(InfixApply _ op2 _) = do
  OpPrec fix1 pr1 <- getOpPrec op1
  OpPrec fix2 pr2 <- getOpPrec op2
  unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR) $
    report $ errAmbiguousParse "operator" (opName op1) (opName op2)
  return $ RightSection op1 e
checkRSection op e = return $ RightSection op e

-- The functions 'fixPrecT' and 'fixRPrecT' check the relative precedences
-- of adjacent infix operators in patterns. The patterns will be reordered
-- such that the infix operator with the lowest precedence becomes the root
-- of the term. The functions rely on the fact that the parser constructs
-- infix patterns in a right-associative fashion, i.e., the left argument
-- of an infix pattern will never be an infix pattern. The functions also
-- check whether the left and right arguments of an infix pattern are negative
-- literals. In this case, the negation must bind more tightly than the
-- operator for the pattern to be accepted.

fixPrecT :: (Pattern a -> QualIdent -> Pattern a -> Pattern a)
         -> Pattern a -> QualIdent -> Pattern a -> PCM (Pattern a)
fixPrecT infixpatt t1@(NegativePattern _ _ _) op t2 = do
  OpPrec fix pr <- prec op <$> getPrecEnv
  unless (pr < 6 || pr == 6 && fix == InfixL) $
    report $ errInvalidParse "unary operator" minusId op
  fixRPrecT infixpatt t1 op t2
fixPrecT infixpatt t1 op t2 = fixRPrecT infixpatt t1 op t2

fixRPrecT :: (Pattern a -> QualIdent -> Pattern a -> Pattern a)
          -> Pattern a -> QualIdent -> Pattern a -> PCM (Pattern a)
fixRPrecT infixpatt t1 op t2@(NegativePattern _ _ _) = do
  OpPrec _ pr <- prec op <$> getPrecEnv
  unless (pr < 6) $ report $ errInvalidParse "unary operator" minusId op
  return $ infixpatt t1 op t2
fixRPrecT infixpatt t1 op1 (InfixPattern a t2 op2 t3) = do
  OpPrec fix1 pr1 <- prec op1 <$> getPrecEnv
  OpPrec fix2 pr2 <- prec op2 <$> getPrecEnv
  if pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR
    then return $ infixpatt t1 op1 (InfixPattern a t2 op2 t3)
    else if pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL
      then do
        left <- fixPrecT infixpatt t1 op1 t2
        return $ InfixPattern a left op2 t3
      else do
        report $ errAmbiguousParse "operator" op1 op2
        return $ infixpatt t1 op1 (InfixPattern a t2 op2 t3)
fixRPrecT infixpatt t1 op1 (InfixFuncPattern a t2 op2 t3) = do
  OpPrec fix1 pr1 <- prec op1 <$> getPrecEnv
  OpPrec fix2 pr2 <- prec op2 <$> getPrecEnv
  if pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR
    then return $ infixpatt t1 op1 (InfixFuncPattern a t2 op2 t3)
    else if pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL
      then do
        left <- fixPrecT infixpatt t1 op1 t2
        return $ InfixFuncPattern a left op2 t3
      else do
        report $ errAmbiguousParse "operator" op1 op2
        return $ infixpatt t1 op1 (InfixFuncPattern a t2 op2 t3)
fixRPrecT infixpatt t1 op t2 = return $ infixpatt t1 op t2

{-fixPrecT :: Position -> OpPrecEnv -> Pattern -> QualIdent -> Pattern
         -> Pattern
fixPrecT p pEnv t1@(NegativePattern uop l) op t2
  | pr < 6 || pr == 6 && fix == InfixL = fixRPrecT p pEnv t1 op t2
  | otherwise = errorAt p $ errInvalidParse "unary" uop op
  where OpPrec fix pr = prec op pEnv
fixPrecT p pEnv t1 op t2 = fixRPrecT p pEnv t1 op t2-}

{-fixRPrecT :: Position -> OpPrecEnv -> Pattern -> QualIdent -> Pattern
          -> Pattern
fixRPrecT p pEnv t1 op t2@(NegativePattern uop l)
  | pr < 6 = InfixPattern t1 op t2
  | otherwise = errorAt p $ errInvalidParse "unary" uop op
  where OpPrec _ pr = prec op pEnv
fixRPrecT p pEnv t1 op1 (InfixPattern t2 op2 t3)
  | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR =
      InfixPattern t1 op1 (InfixPattern t2 op2 t3)
  | pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL =
      InfixPattern (fixPrecT p pEnv t1 op1 t2) op2 t3
  | otherwise = errorAt p $ errAmbiguousParse "operator" op1 op2
  where OpPrec fix1 pr1 = prec op1 pEnv
        OpPrec fix2 pr2 = prec op2 pEnv
fixRPrecT _ _ t1 op t2 = InfixPattern t1 op t2-}

-- The functions 'checkOpL' and 'checkOpR' check the left and right arguments
-- of an operator declaration. If they are infix patterns they must bind
-- more tightly than the operator, otherwise the left-hand side of the
-- declaration is invalid.

checkOpL :: Ident -> Pattern a -> PCM (Pattern a)
checkOpL op t@(NegativePattern _ _ _) = do
  OpPrec fix pr <- prec (qualify op) <$> getPrecEnv
  unless (pr < 6 || pr == 6 && fix == InfixL) $
    report $ errInvalidParse "unary operator" minusId (qualify op)
  return t
checkOpL op1 t@(InfixPattern _ _ op2 _) = do
  OpPrec fix1 pr1 <- prec (qualify op1) <$> getPrecEnv
  OpPrec fix2 pr2 <- prec op2 <$> getPrecEnv
  unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL) $
    report $ errInvalidParse "operator" op1 op2
  return t
checkOpL _ t = return t

checkOpR :: Ident -> Pattern a -> PCM (Pattern a)
checkOpR op t@(NegativePattern _ _ _) = do
  OpPrec _ pr <- prec (qualify op)  <$> getPrecEnv
  when (pr >= 6) $ report $ errInvalidParse "unary operator" minusId (qualify op)
  return t
checkOpR op1 t@(InfixPattern _ _ op2 _) = do
  OpPrec fix1 pr1 <- prec (qualify op1)  <$> getPrecEnv
  OpPrec fix2 pr2 <- prec op2  <$> getPrecEnv
  unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR) $
    report $ errInvalidParse "operator" op1 op2
  return t
checkOpR _ t = return t

-- The functions 'opPrec' and 'prec' return the fixity and operator precedence
-- of an entity. Even though precedence checking is performed after the
-- renaming phase, we have to be prepared to see ambiguous identifiers here.
-- This may happen while checking the root of an operator definition that
-- shadows an imported definition.

getOpPrec :: InfixOp a -> PCM OpPrec
getOpPrec op = opPrec op <$> getPrecEnv

opPrec :: InfixOp a -> OpPrecEnv -> OpPrec
opPrec op = prec (opName op)

prec :: QualIdent -> OpPrecEnv -> OpPrec
prec op env = case qualLookupP op env of
  [] -> defaultP
  PrecInfo _ p : _ -> p

-- ---------------------------------------------------------------------------
-- Error messages
-- ---------------------------------------------------------------------------

errUndefinedOperator :: Ident -> Message
errUndefinedOperator op = posMessage op $ hsep $ map text
  ["No definition for", escName op, "in this scope"]

errMultiplePrecedence :: [Ident] -> Message
errMultiplePrecedence []       = internalError
  "PrecCheck.errMultiplePrecedence: empty list"
errMultiplePrecedence (op:ops) = posMessage op $
  (hsep $ map text ["More than one fixity declaration for", escName op, "at"])
  $+$ nest 2 (vcat (map (ppPosition . getPosition) (op:ops)))

errInvalidParse :: String -> Ident -> QualIdent -> Message
errInvalidParse what op1 op2 = posMessage op1 $ hsep $ map text
  [ "Invalid use of", what, escName op1, "with", escQualName op2, "in"
  , showLine $ qidPosition op2]

-- FIXME: Messages may have missing positions for minus operators

errAmbiguousParse :: String -> QualIdent -> QualIdent -> Message
errAmbiguousParse what op1 op2 = posMessage op1 $ hsep $ map text
  ["Ambiguous use of", what, escQualName op1, "with", escQualName op2, "in"
  , showLine $ qidPosition op2]
