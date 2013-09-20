% $Id: PrecCheck.lhs,v 1.21 2004/02/15 22:10:34 wlux Exp $
%
% Copyright (c) 2001-2004, Wolfgang Lux
%                    2013, Matthias Böhm
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
% Modified by Björn Peemöller (bjp@informatik.uni-kiel.de)
%
\nwfilename{PrecCheck.lhs}
\section{Checking Precedences of Infix Operators}
The parser does not know the relative precedences of infix operators
and therefore parses them as if they all associate to the right and
have the same precedence. After performing the definition checks,
the compiler is going to process the infix applications in the module
and rearrange infix applications according to the relative precedences
of the operators involved.
\begin{verbatim}

> module Checks.PrecCheck (precCheck) where

> import Control.Monad (liftM, liftM2, liftM3, unless, when)
> import qualified Control.Monad.State as S (State, runState, gets, modify)
> import Data.List (partition)
> import Text.PrettyPrint

> import Curry.Base.Ident
> import Curry.Base.Position
> import Curry.Syntax

> import Base.Expr
> import Base.Messages (Message, posMessage)
> import Base.Utils (findDouble)

> import Env.OpPrec (OpPrecEnv, OpPrec (..), PrecInfo (..), defaultP, bindP
>   , qualLookupP)

> precCheck :: ModuleIdent -> OpPrecEnv -> [Decl] -> ([Decl], OpPrecEnv, [Message])
> precCheck m pEnv decls = runPCM (checkDecls decls) initState
>  where initState = PCState m pEnv []

\end{verbatim}
The Prec check monad.
\begin{verbatim}

> data PCState = PCState
>   { moduleIdent :: ModuleIdent
>   , precEnv     :: OpPrecEnv
>   , errors      :: [Message]
>   }

> type PCM = S.State PCState -- the Prec Check Monad

> runPCM :: PCM a -> PCState -> (a, OpPrecEnv, [Message])
> runPCM kcm s = let (a, s') = S.runState kcm s
>                in  (a, precEnv s', reverse $ errors s')

> getModuleIdent :: PCM ModuleIdent
> getModuleIdent = S.gets moduleIdent

> getPrecEnv :: PCM OpPrecEnv
> getPrecEnv = S.gets precEnv

> modifyPrecEnv :: (OpPrecEnv -> OpPrecEnv) -> PCM ()
> modifyPrecEnv f = S.modify $ \ s -> s { precEnv = f $ precEnv s }

> withLocalPrecEnv :: PCM a -> PCM a
> withLocalPrecEnv act = do
>   oldEnv <- getPrecEnv
>   res <- act
>   modifyPrecEnv $ const oldEnv
>   return res

> report :: Message -> PCM ()
> report err = S.modify (\ s -> s { errors = err : errors s })

\end{verbatim}
For each declaration group, including the module-level, the compiler
first checks that its fixity declarations contain no duplicates and
that there is a corresponding value or constructor declaration in that
group. The fixity declarations are then used for extending the
imported precedence environment.
\begin{verbatim}

> bindPrecs :: [Decl] -> PCM ()
> bindPrecs ds = case findDouble opFixDecls of
>   Just op -> report $ errDuplicatePrecedence op
>   Nothing -> case filter (`notElem` bvs) opFixDecls of
>     op : _ -> report $ errUndefinedOperator op
>     []     -> do
>       m <- getModuleIdent
>       modifyPrecEnv $ \ env -> foldr (bindPrec m) env fixDs
>   where
>     (fixDs, nonFixDs) = partition isInfixDecl ds
>     opFixDecls        = [ op | InfixDecl _ _ _ ops <- fixDs, op <- ops]
>     bvs               = concatMap boundValues nonFixDs

> bindPrec :: ModuleIdent -> Decl -> OpPrecEnv -> OpPrecEnv
> bindPrec m (InfixDecl _ fix prc ops) pEnv
>   | p == defaultP = pEnv
>   | otherwise     = foldr (flip (bindP m) p) pEnv ops
>   where p = OpPrec fix prc
> bindPrec _ _ pEnv = pEnv

> boundValues :: Decl -> [Ident]
> boundValues (DataDecl      _ _ _ cs _) = map constr cs
>   where constr (ConstrDecl _ _   c  _) = c
>         constr (ConOpDecl  _ _ _ op _) = op
> boundValues (NewtypeDecl _ _ _ (NewConstrDecl _ _ c _) _) = [c]
> boundValues (FunctionDecl _ _ _ f _) = [f]
> boundValues (ForeignDecl  _ _ _ f _) = [f]
> boundValues (ExternalDecl      _ fs) = fs
> boundValues (PatternDecl  _ _ _ t _) = bv t
> boundValues (FreeDecl          _ vs) = vs
> boundValues (ClassDecl   _ _ _ _ ds) = concatMap tysig ds
>   where tysig (TypeSig _ _ ids _ _) = ids
>         tysig _                     = [] 
> boundValues _                        = []

\end{verbatim}
With the help of the precedence environment, the compiler checks all
infix applications and sections in the program. This pass will modify
the parse tree such that for a nested infix application the operator
with the lowest precedence becomes the root and that two adjacent
operators with the same precedence will not have conflicting
associativities. Note that the top-level precedence environment has to
be returned because it is needed for constructing the module's
interface.
\begin{verbatim}

> checkDecls :: [Decl] -> PCM [Decl]
> checkDecls decls = bindPrecs decls >> mapM checkDecl decls

> checkDecl :: Decl -> PCM Decl
> checkDecl (FunctionDecl p cty id0 f eqs) =
>   FunctionDecl p cty id0 f `liftM` mapM checkEquation eqs
> checkDecl (PatternDecl p cty id0 t rhs) =
>   liftM2 (PatternDecl p cty id0) (checkPattern t) (checkRhs rhs)
> checkDecl (ClassDecl p scon cls tyvar decls) = 
>   ClassDecl p scon cls tyvar `liftM` mapM checkDecl decls
> checkDecl (InstanceDecl p scon cls tycon ids decls) = 
>   InstanceDecl p scon cls tycon ids `liftM` mapM checkDecl decls
> checkDecl d                      = return d

> checkEquation :: Equation -> PCM Equation
> checkEquation (Equation p lhs rhs) =
>   liftM2 (Equation p) (checkLhs lhs) (checkRhs rhs)

> checkLhs :: Lhs -> PCM Lhs
> checkLhs (FunLhs    f ts) = FunLhs f `liftM` mapM checkPattern ts
> checkLhs (OpLhs t1 op t2) =
>   liftM2 (flip OpLhs op) (checkPattern t1 >>= checkOpL op)
>                          (checkPattern t2 >>= checkOpR op)
> checkLhs (ApLhs   lhs ts) =
>   liftM2 ApLhs (checkLhs lhs) (mapM checkPattern ts)

> checkPattern :: Pattern -> PCM Pattern
> checkPattern l@(LiteralPattern      _) = return l
> checkPattern n@(NegativePattern   _ _) = return n
> checkPattern v@(VariablePattern     _) = return v
> checkPattern (ConstructorPattern c ts) =
>   ConstructorPattern c `liftM` mapM checkPattern ts
> checkPattern (InfixPattern   t1 op t2) = do
>   t1' <- checkPattern t1
>   t2' <- checkPattern t2
>   fixPrecT InfixPattern t1' op t2'
> checkPattern (ParenPattern          t) =
>   ParenPattern `liftM` checkPattern t
> checkPattern (TuplePattern       p ts) =
>   TuplePattern p `liftM` mapM checkPattern ts
> checkPattern (ListPattern        p ts) =
>   ListPattern p `liftM` mapM checkPattern ts
> checkPattern (AsPattern           v t) =
>   AsPattern v `liftM` checkPattern t
> checkPattern (LazyPattern         p t) =
>   LazyPattern p `liftM` checkPattern t
> checkPattern (FunctionPattern    f ts) =
>   FunctionPattern f `liftM` mapM checkPattern ts
> checkPattern (InfixFuncPattern t1 op t2) = do
>   t1' <- checkPattern t1
>   t2' <- checkPattern t2
>   fixPrecT InfixFuncPattern t1' op t2'
> checkPattern (RecordPattern       fs r) =
>   liftM2 RecordPattern (mapM checkFieldPattern fs) $
>     case r of
>       Nothing -> return Nothing
>       Just r' -> Just `fmap` checkPattern r'

> checkFieldPattern :: Field Pattern -> PCM (Field Pattern)
> checkFieldPattern (Field p l e) = Field p l `liftM` checkPattern e

> checkRhs :: Rhs -> PCM Rhs
> checkRhs (SimpleRhs p e ds) = withLocalPrecEnv $
>   liftM2 (flip (SimpleRhs p)) (checkDecls ds) (checkExpr e)
> checkRhs (GuardedRhs es ds) = withLocalPrecEnv $
>   liftM2 (flip GuardedRhs) (checkDecls ds) (mapM checkCondExpr es)

> checkCondExpr :: CondExpr -> PCM CondExpr
> checkCondExpr (CondExpr p g e) =
>   liftM2 (CondExpr p) (checkExpr g) (checkExpr e)

> checkExpr :: Expression -> PCM Expression
> checkExpr l@(Literal     _) = return l
> checkExpr v@(Variable  _ _) = return v
> checkExpr c@(Constructor _) = return c
> checkExpr (Paren    e) = Paren `liftM` checkExpr e
> checkExpr (Typed cty e cx ty) = liftM3 (Typed cty) (checkExpr e) (return cx) (return ty)
> checkExpr (Tuple p es) = Tuple p `liftM` mapM checkExpr es
> checkExpr (List  p es) = List  p `liftM` mapM checkExpr es
> checkExpr (ListCompr p e qs) = withLocalPrecEnv $
>   liftM2 (flip (ListCompr p)) (mapM checkStmt qs) (checkExpr e)
> checkExpr (EnumFrom cty          e) = EnumFrom cty `liftM` checkExpr e
> checkExpr (EnumFromThen cty  e1 e2) =
>   liftM2 (EnumFromThen cty) (checkExpr e1) (checkExpr e2)
> checkExpr (EnumFromTo cty    e1 e2) =
>   liftM2 (EnumFromTo cty) (checkExpr e1) (checkExpr e2)
> checkExpr (EnumFromThenTo cty e1 e2 e3) =
>   liftM3 (EnumFromThenTo cty) (checkExpr e1) (checkExpr e2) (checkExpr e3)
> checkExpr (UnaryMinus         op e) = UnaryMinus op `liftM` (checkExpr e)
> checkExpr (Apply e1 e2) =
>   liftM2 Apply (checkExpr e1) (checkExpr e2)
> checkExpr (InfixApply e1 op e2) = do
>   e1' <- checkExpr e1
>   e2' <- checkExpr e2
>   fixPrec e1' op e2'
> checkExpr (LeftSection      e op) = checkExpr e >>= checkLSection op
> checkExpr (RightSection     op e) = checkExpr e >>= checkRSection op
> checkExpr (Lambda         r ts e) =
>   liftM2 (Lambda r) (mapM checkPattern ts) (checkExpr e)
> checkExpr (Let              ds e) = withLocalPrecEnv $
>   liftM2 Let (checkDecls ds) (checkExpr e)
> checkExpr (Do              sts e) = withLocalPrecEnv $
>   liftM2 Do  (mapM checkStmt sts) (checkExpr e)
> checkExpr (IfThenElse r e1 e2 e3) =
>   liftM3 (IfThenElse r) (checkExpr e1) (checkExpr e2) (checkExpr e3)
> checkExpr (Case      r ct e alts) =
>   liftM2 (Case r ct) (checkExpr e) (mapM checkAlt alts)
> checkExpr (RecordConstr       fs) =
>   RecordConstr `liftM` mapM checkFieldExpr fs
> checkExpr (RecordSelection   e l) =
>   flip RecordSelection l `liftM` checkExpr e
> checkExpr (RecordUpdate     fs e) =
>   liftM2 RecordUpdate (mapM checkFieldExpr fs) (checkExpr e)

> checkFieldExpr :: Field Expression -> PCM (Field Expression)
> checkFieldExpr (Field p l e) = Field p l `liftM` checkExpr e

> checkStmt :: Statement -> PCM Statement
> checkStmt (StmtExpr   p e) = StmtExpr p `liftM` checkExpr e
> checkStmt (StmtDecl    ds) = StmtDecl `liftM` checkDecls ds
> checkStmt (StmtBind p t e) =
>   liftM2 (StmtBind p) (checkPattern t) (checkExpr e)

> checkAlt :: Alt -> PCM Alt
> checkAlt (Alt p t rhs) = liftM2 (Alt p) (checkPattern t) (checkRhs rhs)

\end{verbatim}
The functions \texttt{fixPrec}, \texttt{fixUPrec}, and
\texttt{fixRPrec} check the relative precedences of adjacent infix
operators in nested infix applications and unary negations. The
expressions will be reordered such that the infix operator with the
lowest precedence becomes the root of the expression. \emph{The
functions rely on the fact that the parser constructs infix
applications in a right-associative fashion}, i.e., the left argument
of an infix application will never be an infix application. In
addition, a unary negation will never have an infix application as
its argument.

The function \texttt{fixPrec} checks whether the left argument of an
infix application is a unary negation and eventually reorders the
expression if the precedence of the infix operator is higher than that
of the negation. This will be done with the help of the function
\texttt{fixUPrec}. In any case, the function \texttt{fixRPrec} is used
for fixing the precedence of the infix operator and that of its right
argument. Note that both arguments already have been checked before
\texttt{fixPrec} is called.
\begin{verbatim}

> fixPrec :: Expression -> InfixOp -> Expression -> PCM Expression
> fixPrec (UnaryMinus uop e1) op e2 = do
>   OpPrec fix pr <- getOpPrec op
>   if pr < 6 || pr == 6 && fix == InfixL
>     then fixRPrec (UnaryMinus uop e1) op e2
>     else if pr > 6
>       then fixUPrec uop e1 op e2
>       else do
>         report $ errAmbiguousParse "unary" (qualify uop) (opName op)
>         return $ InfixApply (UnaryMinus uop e1) op e2
> fixPrec e1 op e2 = fixRPrec e1 op e2

> fixUPrec :: Ident -> Expression -> InfixOp -> Expression -> PCM Expression
> fixUPrec uop e1 op e2@(UnaryMinus _ _) = do
>   report $ errAmbiguousParse "operator" (opName op) (qualify uop)
>   return $ UnaryMinus uop (InfixApply e1 op e2)
> fixUPrec uop e1 op1 e'@(InfixApply e2 op2 e3) = do
>   OpPrec fix2 pr2 <- getOpPrec op2
>   if pr2 < 6 || pr2 == 6 && fix2 == InfixL
>     then do
>       left <- fixUPrec uop e1 op1 e2
>       return $ InfixApply left op2 e3
>     else if pr2 > 6
>       then do
>         op <- fixRPrec e1 op1 $ InfixApply e2 op2 e3
>         return $ UnaryMinus uop op
>       else do
>         report $ errAmbiguousParse "unary" (qualify uop) (opName op2)
>         return $ InfixApply (UnaryMinus uop e1) op1 e'
> fixUPrec uop e1 op e2 = return $ UnaryMinus uop (InfixApply e1 op e2)

> fixRPrec :: Expression -> InfixOp -> Expression -> PCM Expression
> fixRPrec e1 op (UnaryMinus uop e2) = do
>   OpPrec _ pr <- getOpPrec op
>   unless (pr < 6) $ report $ errAmbiguousParse "operator" (opName op) (qualify uop)
>   return $ InfixApply e1 op $ UnaryMinus uop e2
> fixRPrec e1 op1 (InfixApply e2 op2 e3) = do
>   OpPrec fix1 pr1 <- getOpPrec op1
>   OpPrec fix2 pr2 <- getOpPrec op2
>   if pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR
>      then return $ InfixApply e1 op1 $ InfixApply e2 op2 e3
>      else if pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL
>        then do
>           left <- fixPrec e1 op1 e2
>           return $ InfixApply left op2 e3
>        else do
>          report $ errAmbiguousParse "operator" (opName op1) (opName op2)
>          return $ InfixApply e1 op1 $ InfixApply e2 op2 e3
> fixRPrec e1 op e2 = return $ InfixApply e1 op e2

\end{verbatim}
The functions \texttt{checkLSection} and \texttt{checkRSection} are
used for handling the precedences inside left and right sections.
These functions only need to check that an infix operator occurring in
the section has either a higher precedence than the section operator
or both operators have the same precedence and are both left
associative for a left section and right associative for a right
section, respectively.
\begin{verbatim}

> checkLSection :: InfixOp -> Expression -> PCM Expression
> checkLSection op e@(UnaryMinus uop _) = do
>   OpPrec fix pr <- getOpPrec op
>   unless (pr < 6 || pr == 6 && fix == InfixL) $
>     report $ errAmbiguousParse "unary" (qualify uop) (opName op)
>   return $ LeftSection e op
> checkLSection op1 e@(InfixApply _ op2 _) = do
>   OpPrec fix1 pr1 <- getOpPrec op1
>   OpPrec fix2 pr2 <- getOpPrec op2
>   unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL) $
>     report $ errAmbiguousParse "operator" (opName op1) (opName op2)
>   return $ LeftSection e op1
> checkLSection op e = return $ LeftSection e op

> checkRSection :: InfixOp -> Expression -> PCM Expression
> checkRSection op e@(UnaryMinus uop _) = do
>   OpPrec _ pr <- getOpPrec op
>   unless (pr < 6) $ report $ errAmbiguousParse "unary" (qualify uop) (opName op)
>   return $ RightSection op e
> checkRSection op1 e@(InfixApply _ op2 _) = do
>   OpPrec fix1 pr1 <- getOpPrec op1
>   OpPrec fix2 pr2 <- getOpPrec op2
>   unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR) $
>     report $ errAmbiguousParse "operator" (opName op1) (opName op2)
>   return $ RightSection op1 e
> checkRSection op e = return $ RightSection op e

\end{verbatim}
The functions \texttt{fixPrecT} and \texttt{fixRPrecT} check the
relative precedences of adjacent infix operators in patterns. The
patterns will be reordered such that the infix operator with the
lowest precedence becomes the root of the term. \emph{The functions
rely on the fact that the parser constructs infix patterns in a
right-associative fashion}, i.e., the left argument of an infix pattern
will never be an infix pattern. The functions also check whether the
left and right arguments of an infix pattern are negative literals. In
this case, the negation must bind more tightly than the operator for
the pattern to be accepted.
\begin{verbatim}

> fixPrecT :: (Pattern -> QualIdent -> Pattern -> Pattern)
>          -> Pattern -> QualIdent -> Pattern -> PCM Pattern
> fixPrecT infixpatt t1@(NegativePattern uop _) op t2 = do
>   OpPrec fix pr <- prec op `liftM` getPrecEnv
>   unless (pr < 6 || pr == 6 && fix == InfixL) $
>     report $ errInvalidParse "unary" uop op
>   fixRPrecT infixpatt t1 op t2
> fixPrecT infixpatt t1 op t2 = fixRPrecT infixpatt t1 op t2

> fixRPrecT :: (Pattern -> QualIdent -> Pattern -> Pattern)
>           -> Pattern  -> QualIdent -> Pattern -> PCM Pattern
> fixRPrecT infixpatt t1 op t2@(NegativePattern uop _) = do
>   OpPrec _ pr <- prec op `liftM` getPrecEnv
>   unless (pr < 6) $ report $ errInvalidParse "unary" uop op
>   return $ infixpatt t1 op t2
> fixRPrecT infixpatt t1 op1 (InfixPattern t2 op2 t3) = do
>   OpPrec fix1 pr1 <- prec op1 `liftM` getPrecEnv
>   OpPrec fix2 pr2 <- prec op2 `liftM` getPrecEnv
>   if pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR
>     then return $ infixpatt t1 op1 (InfixPattern t2 op2 t3)
>     else if pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL
>       then do
>         left <- fixPrecT infixpatt t1 op1 t2
>         return $ InfixPattern left op2 t3
>       else do
>         report $ errAmbiguousParse "operator" op1 op2
>         return $ infixpatt t1 op1 (InfixPattern t2 op2 t3)
> fixRPrecT infixpatt t1 op1 (InfixFuncPattern t2 op2 t3) = do
>   OpPrec fix1 pr1 <- prec op1 `liftM` getPrecEnv
>   OpPrec fix2 pr2 <- prec op2 `liftM` getPrecEnv
>   if pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR
>     then return $ infixpatt t1 op1 (InfixFuncPattern t2 op2 t3)
>     else if pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL
>       then do
>         left <- fixPrecT infixpatt t1 op1 t2
>         return $ InfixFuncPattern left op2 t3
>       else do
>         report $ errAmbiguousParse "operator" op1 op2
>         return $ infixpatt t1 op1 (InfixFuncPattern t2 op2 t3)
> fixRPrecT infixpatt t1 op t2 = return $ infixpatt t1 op t2

> {-fixPrecT :: Position -> OpPrecEnv -> Pattern -> QualIdent -> Pattern
>          -> Pattern
> fixPrecT p pEnv t1@(NegativePattern uop l) op t2
>   | pr < 6 || pr == 6 && fix == InfixL = fixRPrecT p pEnv t1 op t2
>   | otherwise = errorAt p $ errInvalidParse "unary" uop op
>   where OpPrec fix pr = prec op pEnv
> fixPrecT p pEnv t1 op t2 = fixRPrecT p pEnv t1 op t2-}

> {-fixRPrecT :: Position -> OpPrecEnv -> Pattern -> QualIdent -> Pattern
>           -> Pattern
> fixRPrecT p pEnv t1 op t2@(NegativePattern uop l)
>   | pr < 6 = InfixPattern t1 op t2
>   | otherwise = errorAt p $ errInvalidParse "unary" uop op
>   where OpPrec _ pr = prec op pEnv
> fixRPrecT p pEnv t1 op1 (InfixPattern t2 op2 t3)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR =
>       InfixPattern t1 op1 (InfixPattern t2 op2 t3)
>   | pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL =
>       InfixPattern (fixPrecT p pEnv t1 op1 t2) op2 t3
>   | otherwise = errorAt p $ errAmbiguousParse "operator" op1 op2
>   where OpPrec fix1 pr1 = prec op1 pEnv
>         OpPrec fix2 pr2 = prec op2 pEnv
> fixRPrecT _ _ t1 op t2 = InfixPattern t1 op t2-}

\end{verbatim}
The functions \texttt{checkOpL} and \texttt{checkOpR} check the left
and right arguments of an operator declaration. If they are infix
patterns they must bind more tightly than the operator, otherwise the
left-hand side of the declaration is invalid.
\begin{verbatim}

> checkOpL :: Ident -> Pattern -> PCM Pattern
> checkOpL op t@(NegativePattern uop _) = do
>   OpPrec fix pr <- prec (qualify op) `liftM` getPrecEnv
>   unless (pr < 6 || pr == 6 && fix == InfixL) $
>     report $ errInvalidParse "unary" uop (qualify op)
>   return t
> checkOpL op1 t@(InfixPattern _ op2 _) = do
>   OpPrec fix1 pr1 <- prec (qualify op1) `liftM` getPrecEnv
>   OpPrec fix2 pr2 <- prec op2 `liftM` getPrecEnv
>   unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL) $
>     report $ errInvalidParse "operator" op1 op2
>   return t
> checkOpL _ t = return t

> checkOpR :: Ident -> Pattern -> PCM Pattern
> checkOpR op t@(NegativePattern uop _) = do
>   OpPrec _ pr <- prec (qualify op)  `liftM` getPrecEnv
>   when (pr >= 6) $ report $ errInvalidParse "unary" uop (qualify op)
>   return t
> checkOpR op1 t@(InfixPattern _ op2 _) = do
>   OpPrec fix1 pr1 <- prec (qualify op1)  `liftM` getPrecEnv
>   OpPrec fix2 pr2 <- prec op2  `liftM` getPrecEnv
>   unless (pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR) $
>     report $ errInvalidParse "operator" op1 op2
>   return t
> checkOpR _ t = return t

\end{verbatim}
The functions \texttt{opPrec} and \texttt{prec} return the fixity and
operator precedence of an entity. Even though precedence checking is
performed after the renaming phase, we have to be prepared to see
ambiguous identifiers here. This may happen while checking the root of
an operator definition that shadows an imported definition.
\begin{verbatim}

> getOpPrec :: InfixOp -> PCM OpPrec
> getOpPrec op = opPrec op `liftM` getPrecEnv

> opPrec :: InfixOp -> OpPrecEnv -> OpPrec
> opPrec op = prec (opName op)

> prec :: QualIdent -> OpPrecEnv -> OpPrec
> prec op env = case qualLookupP op env of
>   [] -> defaultP
>   PrecInfo _ p : _ -> p

\end{verbatim}
Error messages.
\begin{verbatim}

> errUndefinedOperator :: Ident -> Message
> errUndefinedOperator op = posMessage op $ hsep $ map text
>   ["No definition for", idName op, "in this scope"]

> errDuplicatePrecedence :: Ident -> Message
> errDuplicatePrecedence op = posMessage op $ hsep $ map text
>   ["More than one fixity declaration for", idName op]

> errInvalidParse :: String -> Ident -> QualIdent -> Message
> errInvalidParse what op1 op2 = posMessage op1 $ hsep $ map text
>   [ "Invalid use of", what, idName op1, "with", qualName op2
>   , showLine $ qidPosition op2]

> errAmbiguousParse :: String -> QualIdent -> QualIdent -> Message
> errAmbiguousParse what op1 op2 = posMessage op1 $ hsep $ map text
>   ["Ambiguous use of", what, qualName op1, "with", qualName op2
>   , showLine $ qidPosition op2]

\end{verbatim}
