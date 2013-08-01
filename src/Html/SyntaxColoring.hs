module Html.SyntaxColoring
  ( Program, Code (..), TypeKind (..), ConstructorKind (..)
  , IdentifierKind (..), FunctionKind (..)
  , genProgram, code2string, getQualIdent
  ) where

import Data.Char hiding (Space)
import Data.Function (on)
import Data.List (intercalate, nubBy, partition)
import Data.Maybe (fromMaybe, mapMaybe)
import Debug.Trace (trace)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Base.Message
import Curry.Syntax

import Base.Messages

debug :: Bool
debug = False -- mergen von Token und Codes

trace' :: String -> a -> a
trace' s x = if debug then trace s x else x

debug' :: Bool
debug' = False -- messages

trace'' :: String -> a -> a
trace'' s x = if debug' then trace s x else x

type Program = [(Int, Int, Code)]

data Code
  = Keyword String
  | Space Int
  | NewLine
  | ConstructorName ConstructorKind QualIdent
  | TypeConstructor TypeKind QualIdent
  | Function FunctionKind QualIdent
  | ModuleName ModuleIdent
  | Commentary String
  | NumberCode String
  | StringCode String
  | CharCode String
  | Symbol String
  | Identifier IdentifierKind QualIdent
  | CodeWarning [Message] Code
  | NotParsed String
    deriving Show

data TypeKind
  = TypeDecla
  | TypeUse
  | TypeExport
    deriving Show

data ConstructorKind
  = ConstrPattern
  | ConstrCall
  | ConstrDecla
  | OtherConstrKind
    deriving Show

data IdentifierKind
  = IdDecl
  | IdOccur
  | UnknownId
    deriving Show

data FunctionKind
  = InfixFunction
  | TypSig
  | FunDecl
  | FunctionCall
  | OtherFunctionKind
    deriving Show

--- @param src
--- @param list with parse-Results with descending quality,
---        e.g. [typingParse, fullParse, parse]
--- @param lex-Result
--- @return program
genProgram :: String -> [MessageM Module] -> MessageM [(Position, Token)] -> Program
genProgram src parseResults lexed = case runMsg lexed of
  Left e -> buildMessagesIntoPlainText [e] src
  Right (posNtokList, mess) ->
    let messages = (prepareMessages (concatMap getMessages parseResults ++ mess))
        mergedMessages = (mergeMessages' (trace' ("Messages: " ++ show messages) messages) posNtokList)
        (nameList,codes) = catIdentifiers parseResults
    in tokenNcodes2codes nameList 1 1 mergedMessages codes

--- @param code
--- @return qid if available
getQualIdent :: Code -> Maybe QualIdent
getQualIdent (ConstructorName _ qid) = Just qid
getQualIdent (Function        _ qid) = Just qid
getQualIdent (Identifier      _ qid) = Just qid
getQualIdent (TypeConstructor _ qid) = Just qid
getQualIdent  _                      = Nothing

-- DEBUGGING----------- wird bald nicht mehr gebraucht

setMessagePosition :: Message -> Message
setMessagePosition m@(Message (Just p) _) = trace'' ("pos:" ++ show p ++ ":" ++ show m) m
setMessagePosition (Message _ m) =
        let mes@(Message pos _) =  (Message (getPositionFromString $ show m) m) in
        trace'' ("pos:" ++ show pos ++ ":" ++ show mes) mes

getPositionFromString :: String -> Maybe Position
getPositionFromString msg =
     if l > 0 && c > 0
          then Just Position{file=f,line=l,column=c,astRef=noRef}
          else Nothing
  where
      f = takeWhile (/= '"') (tail (dropWhile (/= '"') msg))
      l = readInt (takeWhile (/= '.') (drop 7 (dropWhile (/= ',') msg)))
      c = readInt (takeWhile (/= ':') (tail (dropWhile (/= '.') (drop 7 (dropWhile (/= ',') msg)))))


readInt :: String -> Int
readInt s =
      let onlyNum = filter isDigit s in
      if null onlyNum
         then 0
         else read onlyNum :: Int

flatCode :: Code -> Code
flatCode (CodeWarning _ code) = code
flatCode code                 = code

-- ----------Message---------------------------------------

getMessages :: MessageM a -> [Message]
getMessages = either return snd . runMsg --(Result mess _) = mess
-- getMessages (Failure mess) = mess

lessMessage :: Message -> Message -> Bool
lessMessage (Message mPos1 _) (Message mPos2 _) = mPos1 < mPos2

nubMessages :: [Message] -> [Message]
nubMessages = nubBy eqMessage

eqMessage :: Message -> Message -> Bool
eqMessage (Message p1 s1) (Message p2 s2) = (p1 == p2) && (show s1 == show s2)

prepareMessages :: [Message] -> [Message]
prepareMessages = qsort lessMessage . map setMessagePosition . nubMessages


buildMessagesIntoPlainText :: [Message] -> String -> Program
buildMessagesIntoPlainText messages src =
  buildMessagesIntoPlainText' messages (lines src) [] 1
 where
  buildMessagesIntoPlainText' :: [Message] -> [String] -> [String] -> Int -> Program
  buildMessagesIntoPlainText' _ [] [] _ =   []
  buildMessagesIntoPlainText' _ [] postStrs ln =
        [(ln, 1, NotParsed (unlines postStrs))]
  buildMessagesIntoPlainText' [] preStrs postStrs ln =
        [(ln, 1, NotParsed (unlines (preStrs ++ postStrs)))]

  buildMessagesIntoPlainText' messages1 (str:preStrs) postStrs ln =
        let (pre,post) = partition isLeq messages1 in
        if null pre
            then buildMessagesIntoPlainText' post preStrs (postStrs ++ [str]) (ln + 1)
            else (ln,1,NotParsed (unlines postStrs)) :
                (ln,1,CodeWarning pre (NotParsed str)) :
                (ln,1,NewLine) :
                buildMessagesIntoPlainText' post preStrs [] (ln + 1)
    where
    isLeq (Message (Just p) _) = line p <= ln
    isLeq _ = True

--- @param parse-Modules  [typingParse,fullParse,parse]
catIdentifiers :: [MessageM Module] -> ([(ModuleIdent, ModuleIdent)],[Code])
catIdentifiers = catIds . map fst . rights_sc . map runMsg
    where
      catIds [] = ([],[])
      catIds [m] =
          catIdentifiers' m Nothing
      catIds rs@(m:_:_) =
          catIdentifiers' (last rs) (Just m)

-- not in base befoer base4
rights_sc :: [Either a b] -> [b]
rights_sc es = [ x | Right x <- es]

--- @param parse-Module
--- @param Maybe betterParse-Module
catIdentifiers' :: Module -> Maybe Module -> ([(ModuleIdent,ModuleIdent)],[Code])
catIdentifiers' (Module mid maybeExportSpec is decls)
                Nothing =
      let impCodes = concatMap importDecl2codes (qsort lessImportDecl is)
          codes = (concatMap decl2codes (qsort lessDecl decls))
      in (concatMap renamedImports is,
      ModuleName mid :
       maybe [] exportSpec2codes maybeExportSpec ++ impCodes ++ codes)
catIdentifiers' (Module mid maybeExportSpec1 _ _)
                (Just (Module _ maybeExportSpec2 is decls)) =
      let impCodes = concatMap importDecl2codes (qsort lessImportDecl is)
          codes = (concatMap decl2codes (qsort lessDecl decls))
      in (concatMap renamedImports is,
      replaceFunctionCalls $
        map (addModuleIdent mid)
          ([ModuleName mid] ++
           mergeExports2codes
              (maybe [] (\(Exporting _ i) -> i)  maybeExportSpec1)
              (maybe [] (\(Exporting _ i) -> i)  maybeExportSpec2) ++
           impCodes ++ codes))

renamedImports :: ImportDecl -> [(ModuleIdent, ModuleIdent)]
renamedImports (ImportDecl _ oldName _ (Just newName) _) = [(oldName,newName)]
renamedImports _                                         = []

replaceFunctionCalls :: [Code] -> [Code]
replaceFunctionCalls codes = map (idOccur2functionCall qids) codes
   where qids = findFunctionDecls codes


findFunctionDecls :: [Code] -> [QualIdent]
findFunctionDecls = mapMaybe getQualIdent . filter Html.SyntaxColoring.isFunctionDecl . map flatCode

isFunctionDecl :: Code -> Bool
isFunctionDecl (Function FunDecl _) = True
isFunctionDecl _                    = False

idOccur2functionCall :: [QualIdent] -> Code -> Code
idOccur2functionCall qids ide@(Identifier IdOccur qid)
  | isQualified qid = Function FunctionCall qid
  | elem qid qids   = Function FunctionCall qid
  | otherwise       = ide
idOccur2functionCall qids (CodeWarning mess code) =
  CodeWarning mess (idOccur2functionCall qids code)
idOccur2functionCall _ code = code


addModuleIdent :: ModuleIdent -> Code -> Code
addModuleIdent mid c@(Function x qid)
  | hasGlobalScope (unqualify qid) = Function x (qualQualify mid qid)
  | otherwise                      = c
addModuleIdent mid cn@(ConstructorName x qid)
  | not $ isQualified qid = ConstructorName x (qualQualify mid qid)
  | otherwise = cn
addModuleIdent mid tc@(TypeConstructor TypeDecla qid)
  | not $ isQualified qid = TypeConstructor TypeDecla (qualQualify mid qid)
  | otherwise = tc
addModuleIdent mid (CodeWarning mess code) =
    CodeWarning mess (addModuleIdent mid code)
addModuleIdent _ c = c

mergeMessages' :: [Message] -> [(Position,Token)] -> [([Message],Position,Token)]
mergeMessages' _ [] = []
mergeMessages' [] ((p,t):ps) = ([],p,t) : mergeMessages' [] ps
mergeMessages' mss@(m@(Message mPos x):ms) ((p,t):ps)
    | mPos <= Just p = trace' (show mPos ++ " <= " ++ show (Just p) ++ " Message: " ++ show x) ([m],p,t) : mergeMessages' ms ps
    | otherwise = ([],p,t) : mergeMessages' mss ps

tokenNcodes2codes :: [(ModuleIdent,ModuleIdent)] -> Int -> Int -> [([Message],Position,Token)] -> [Code] -> [(Int,Int,Code)]
tokenNcodes2codes _ _ _ [] _ = []
tokenNcodes2codes nameList currLine currCol toks@((messages,Position{line=row,column=col},token):ts) codes
  | currLine < row =
          trace' " NewLine: "
          ((currLine,currCol,NewLine) :
          tokenNcodes2codes nameList (currLine + 1) 1 toks codes)
  | currCol < col =
          trace' (" Space " ++ show (col - currCol))
          ((currLine,currCol,Space (col - currCol)) :
          tokenNcodes2codes nameList currLine col toks codes)
  | isTokenIdentifier token && null codes =
          trace' ("empty Code-List, Token: " ++ show (row,col) ++ show token)
          (addMessage [(currLine,currCol,NotParsed tokenStr)] ++ tokenNcodes2codes nameList newLine newCol ts codes)
  | not (isTokenIdentifier token) =
          trace' (" Token ist kein Identifier: " ++ tokenStr )
          (addMessage [(currLine,currCol,token2code token)] ++ tokenNcodes2codes nameList newLine newCol ts codes)
  | tokenStr == code2string (head codes) =
          trace' (" Code wird genommen: " ++ show (head codes) )
          (addMessage [(currLine,currCol,head codes)] ++ tokenNcodes2codes nameList newLine newCol ts (tail codes))
  | tokenStr == code2qualString (renameModuleIdents nameList (head codes)) =
          let mIdent = maybe Nothing rename (getModuleIdent (head codes))
              lenMod = maybe 0 (length . moduleName) mIdent
              startPos = maybe currCol (const (currCol + lenMod + 1)) mIdent
              symbol = [(currLine,currCol + lenMod,Symbol ".")]
              prefix = maybe []
                            ( (: symbol) .
                              ( \i -> (currLine,
                                        currCol,
                                        ModuleName i)))
                            mIdent in
          trace' (" Code wird genommen: " ++ show (head codes) )
          (addMessage (prefix ++ [(currCol,startPos,head codes)]) ++ tokenNcodes2codes nameList newLine newCol ts (tail codes))
  | elem tokenStr (codeQualifiers (head codes)) =
          trace' (" Token: "++ tokenStr ++" ist Modulname von: " ++ show (head codes) )
          (addMessage [(currLine,currCol,ModuleName (mkMIdent [tokenStr]))] ++
                  tokenNcodes2codes nameList newLine newCol ts codes)
  | otherwise =
          trace' (" Token: "++
                  tokenStr ++
                  ",Code faellt weg:" ++
                  code2string (head codes) ++
                  "|" ++
                  code2qualString (head codes))
          (tokenNcodes2codes nameList currLine currCol toks (tail codes))
  where
      tokenStr = showToken token
      newLine  = (currLine + length (lines tokenStr)) - 1
      newCol   = currCol + length tokenStr

      rename mid = Just $ fromMaybe mid (lookup mid nameList)

      addMessage [] = []
      addMessage ((l,c,code):cs)
         | null messages = (l,c,code):cs
         | otherwise = trace' ("Warning bei code: " ++ show codes ++ ":" ++ show messages)
                              ((l,c,CodeWarning messages code): addMessage cs)
tokenNcodes2codes _ _ _ _ _ = internalError "SyntaxColoring.tokenNcodes2codes: no pattern match"


renameModuleIdents :: [(ModuleIdent,ModuleIdent)] -> Code -> Code
renameModuleIdents nameList c =
    case c of
        Function x qid -> Function x (rename qid (qidModule qid))
        Identifier x qid -> Identifier x (rename qid (qidModule qid))
        _ -> c
  where
    rename x (Nothing) = x
    rename x (Just m) = maybe x (\ m' -> qualifyWith m' (qidIdent x)) (lookup m nameList)

codeQualifiers :: Code -> [String]
codeQualifiers = maybe [] midQualifiers . getModuleIdent

getModuleIdent :: Code -> Maybe ModuleIdent
getModuleIdent (ConstructorName _ qid) = qidModule qid
getModuleIdent (Function        _ qid) = qidModule qid
getModuleIdent (ModuleName        mid) = Just mid
getModuleIdent (Identifier      _ qid) = qidModule qid
getModuleIdent (TypeConstructor _ qid) = qidModule qid
getModuleIdent _                      = Nothing

code2string :: Code -> String
code2string (Keyword           s) = s
code2string (Space               i) = concat (replicate i " ")
code2string NewLine                 = "\n"
code2string (ConstructorName _ qid) = idName $ unqualify qid
code2string (TypeConstructor _ qid) = idName $ unqualify qid
code2string (Function        _ qid) = idName $ unqualify qid
code2string (ModuleName        mid) = moduleName mid
code2string (Commentary        s) = s
code2string (NumberCode        s) = s
code2string (StringCode        s) = s
code2string (CharCode          s) = s
code2string (Symbol            s) = s
code2string (Identifier      _ qid) = idName $ unqualify qid
code2string (CodeWarning       _ c) = code2string c
code2string (NotParsed         s) = s

code2qualString :: Code -> String
code2qualString (ConstructorName _ qid) = qualName qid
code2qualString (Function _ qid) = qualName qid
code2qualString (Identifier _ qid) = qualName qid
code2qualString (TypeConstructor _ qid) = qualName qid
code2qualString x = code2string x

token2code :: Token -> Code
token2code tok@(Token cat _)
  | elem cat [IntTok,FloatTok]
        = NumberCode (showToken tok)
  | elem cat [KW_case,KW_class,KW_data,KW_do,KW_else,KW_external,
              KW_free,KW_if,KW_import,KW_in,KW_infix,KW_infixl,KW_infixr,
              KW_instance, KW_let,KW_module,KW_newtype,KW_of,KW_then,KW_type,
              KW_where,Id_as,Id_ccall,Id_forall,Id_hiding,Id_interface,Id_primitive,
              Id_qualified]
        =  Keyword (showToken tok)
  | elem cat [LeftParen,RightParen,Semicolon,LeftBrace,RightBrace,LeftBracket,
              RightBracket,Comma,Underscore,Backquote,
              At,Colon,DotDot,DoubleColon,Equals,Backslash,Bar,LeftArrow,RightArrow,
              Tilde, DoubleArrow]
        = Symbol (showToken tok)
  | elem cat [LineComment, NestedComment]
        = Commentary (showToken tok)
  | isTokenIdentifier tok
        = Identifier UnknownId $ qualify $ mkIdent $ showToken tok
  | cat == StringTok
        = StringCode (showToken tok)
  | cat == CharTok
        = CharCode (showToken tok)
  | elem cat [EOF,VSemicolon,VRightBrace] = Space 0
  | otherwise = error "SyntaxColoring.token2code: no pattern match"

isTokenIdentifier :: Token -> Bool
isTokenIdentifier (Token cat _) =
  elem cat [Id, QId, Sym, QSym, SymDot, SymMinus, SymMinusDot]

-- DECL Position

declPos :: Decl -> Position
declPos (InfixDecl        p _ _ _  ) = p
declPos (DataDecl         p _ _ _  ) = p
declPos (NewtypeDecl      p _ _ _  ) = p
declPos (TypeDecl         p _ _ _  ) = p
declPos (TypeSig          p _ _ _ _) = p
declPos (FunctionDecl     p _ _ _ _) = p
declPos (ForeignDecl      p _ _ _ _) = p
declPos (ExternalDecl     p _      ) = p
declPos (PatternDecl      p _ _ _ _) = p
declPos (FreeDecl         p _      ) = p
declPos (ClassDecl        p _ _ _ _) = p
declPos (InstanceDecl   p _ _ _ _ _) = p

lessDecl :: Decl -> Decl -> Bool
lessDecl = (<) `on` declPos

lessImportDecl :: ImportDecl -> ImportDecl -> Bool
lessImportDecl = (<) `on` (\ (ImportDecl p _ _ _ _) -> p)

qsort :: (a -> a -> Bool) -> [a] -> [a]
qsort _    []     = []
qsort less (x:xs) = concat [ qsort less [y | y <- xs, less y x]
                           , [x], qsort less [y | y <- xs, not $ less y x]]


-- DECL TO CODE --------------------------------------------------------------------

exportSpec2codes ::  ExportSpec -> [Code]
exportSpec2codes (Exporting _ exports) = concatMap (export2codes []) exports

--- @param parse-Exports
--- @param betterParse-Exports
mergeExports2codes :: [Export] -> [Export]  -> [Code]
mergeExports2codes [] _ = []
mergeExports2codes (e:es) xs = concatMap (export2codes xs)  (e:es)

export2codes :: [Export] -> Export -> [Code]
export2codes exports (Export qid)
    | length (filter checkDouble exports) /= 1 =
       [Identifier UnknownId qid]
    | otherwise =
       let [export] = (filter checkDouble exports) in
       export2c export
  where
    checkDouble (ExportTypeWith q _) = eqQualIdent qid q
    checkDouble (Export q) = eqQualIdent qid q
    checkDouble _ = False

    eqQualIdent q1 q2
      | q1 == q2 = True
      | not (isQualified q1) = unqualify q1 == unqualify q2
      | otherwise = False

    export2c (Export qid1) =
         [Function OtherFunctionKind qid1]
    export2c _ =
         [TypeConstructor TypeExport qid]

export2codes _ (ExportTypeWith qid idents) =
     TypeConstructor TypeExport qid : map (Function OtherFunctionKind . qualify) idents
export2codes _ (ExportTypeAll  qid) =
     [TypeConstructor TypeExport qid]
export2codes _ (ExportModule mid) =
     [ModuleName mid]

importDecl2codes :: ImportDecl -> [Code]
importDecl2codes (ImportDecl _ mid _ mModuleIdent importSpec) =
     [ModuleName mid] ++
     maybe [] ((:[]) . ModuleName) mModuleIdent ++
     maybe [] (importSpec2codes mid)  importSpec

decl2codes :: Decl -> [Code]
decl2codes (InfixDecl _ _ _ ops) = map (Function InfixFunction . qualify) ops
decl2codes (DataDecl _ d vs cds) =
     TypeConstructor TypeDecla (qualify d) :
     map (Identifier UnknownId . qualify) vs ++
     concatMap constrDecl2codes cds
decl2codes (NewtypeDecl _ _ _ _) = []
decl2codes (TypeDecl _ t vs ty) =
     TypeConstructor TypeDecla (qualify t) :
     map (Identifier UnknownId . qualify) vs ++
     typeExpr2codes ty
decl2codes (TypeSig _ _ fs _cx ty) =
     map (Function TypSig . qualify) fs ++ typeExpr2codes ty
decl2codes (FunctionDecl _ _ _ _ eqs) = concatMap equation2codes eqs
decl2codes (ForeignDecl _ _ _ _ _) = []
decl2codes (ExternalDecl     _ fs) = map (Function FunDecl . qualify) fs
decl2codes (PatternDecl _ _ _ p rhs) =  pat2codes p ++ rhs2codes rhs
decl2codes (FreeDecl         _ vs) = map (Identifier IdDecl . qualify) vs
decl2codes (ClassDecl _ _scx _cls _tyvar _decls) = []
decl2codes (InstanceDecl _ _scx _cls _tycon _tyvars _decls) = [] 

equation2codes :: Equation -> [Code]
equation2codes (Equation _ lhs rhs) = lhs2codes lhs ++ rhs2codes rhs

lhs2codes :: Lhs -> [Code]
lhs2codes (FunLhs    f ps) = Function FunDecl (qualify f) : concatMap pat2codes ps
lhs2codes (OpLhs p1 op p2) = pat2codes p1 ++ [Function FunDecl $ qualify op] ++ pat2codes p2
lhs2codes (ApLhs   lhs ps) = lhs2codes lhs ++ concatMap pat2codes ps

rhs2codes :: Rhs -> [Code]
rhs2codes (SimpleRhs _ e ds) = expr2codes e ++ concatMap decl2codes ds
rhs2codes (GuardedRhs ce ds) = concatMap condExpr2codes ce ++ concatMap decl2codes ds

condExpr2codes :: CondExpr -> [Code]
condExpr2codes (CondExpr _ e1 e2) = expr2codes e1 ++ expr2codes e2

pat2codes :: Pattern -> [Code]
pat2codes (LiteralPattern          _) = []
pat2codes (NegativePattern       _ _) = []
pat2codes (VariablePattern         v) = [Identifier IdDecl (qualify v)]
pat2codes (ConstructorPattern qid ps)
  = ConstructorName ConstrPattern qid : concatMap pat2codes ps
pat2codes (InfixPattern    p1 qid p2)
  = pat2codes p1 ++ [ConstructorName ConstrPattern qid] ++ pat2codes p2
pat2codes (ParenPattern            p) = pat2codes p
pat2codes (TuplePattern         _ ps) = concatMap pat2codes ps
pat2codes (ListPattern          _ ps) = concatMap pat2codes ps
pat2codes (AsPattern             v p)
  = Function OtherFunctionKind (qualify v) : pat2codes p
pat2codes (LazyPattern           _ p) = pat2codes p
pat2codes (FunctionPattern    qid ps)
  = Function OtherFunctionKind qid : concatMap pat2codes ps
pat2codes (InfixFuncPattern  p1 f p2)
  = pat2codes p1 ++ [Function InfixFunction f] ++ pat2codes p2
pat2codes (RecordPattern         _ _) =
  internalError "SyntaxColoring.pat2codes: record pattern"

expr2codes :: Expression -> [Code]
expr2codes (Literal               _) = []
expr2codes (Variable          _ qid) = [Identifier IdOccur qid]
expr2codes (Constructor         qid) = [ConstructorName ConstrCall qid]
expr2codes (Paren                 e) = expr2codes e
expr2codes (Typed        _ e _cx ty) = expr2codes e ++ typeExpr2codes ty
expr2codes (Tuple              _ es) = concatMap expr2codes es
expr2codes (List               _ es) = concatMap expr2codes es
expr2codes (ListCompr     _ e stmts) = expr2codes e ++ concatMap statement2codes stmts
expr2codes (EnumFrom              e) = expr2codes e
expr2codes (EnumFromThen      e1 e2) = concatMap expr2codes [e1,e2]
expr2codes (EnumFromTo        e1 e2) = concatMap expr2codes [e1,e2]
expr2codes (EnumFromThenTo e1 e2 e3) = concatMap expr2codes [e1,e2,e3]
expr2codes (UnaryMinus      ident e) = Symbol (idName ident) : expr2codes e
expr2codes (Apply             e1 e2) = expr2codes e1 ++ expr2codes e2
expr2codes (InfixApply     e1 op e2) = expr2codes e1 ++ infixOp2codes op ++ expr2codes e2
expr2codes (LeftSection        e op) = expr2codes e ++ infixOp2codes op
expr2codes (RightSection       op e) = infixOp2codes op ++ expr2codes e
expr2codes (Lambda           _ ps e) = concatMap pat2codes ps ++ expr2codes e
expr2codes (Let                ds e) = concatMap decl2codes ds ++ expr2codes e
expr2codes (Do              stmts e) = concatMap statement2codes stmts ++ expr2codes e
expr2codes (IfThenElse   _ e1 e2 e3) = concatMap expr2codes [e1,e2,e3]
expr2codes (Case         _ _ e alts) = expr2codes e ++ concatMap alt2codes alts
expr2codes _ = internalError "SyntaxColoring.expr2codes: no pattern match"

infixOp2codes :: InfixOp -> [Code]
infixOp2codes (InfixOp   _ qid) = [Function InfixFunction qid]
infixOp2codes (InfixConstr qid) = [ConstructorName OtherConstrKind qid]

statement2codes :: Statement -> [Code]
statement2codes (StmtExpr   _ e) = expr2codes e
statement2codes (StmtDecl    ds) = concatMap decl2codes ds
statement2codes (StmtBind _ p e) = pat2codes p ++ expr2codes e

alt2codes :: Alt -> [Code]
alt2codes (Alt _ p rhs) = pat2codes p ++ rhs2codes rhs

constrDecl2codes :: ConstrDecl -> [Code]
constrDecl2codes (ConstrDecl _ _ c tys)
  = ConstructorName ConstrDecla (qualify c) : concatMap typeExpr2codes tys
constrDecl2codes (ConOpDecl _ _ ty1 op ty2)
  = typeExpr2codes ty1 ++ [ConstructorName ConstrDecla $ qualify op] ++ typeExpr2codes ty2

importSpec2codes :: ModuleIdent -> ImportSpec -> [Code]
importSpec2codes mid (Importing _ is) = concatMap (import2codes mid) is
importSpec2codes mid (Hiding _ is) = concatMap (import2codes mid) is

import2codes :: ModuleIdent -> Import -> [Code]
import2codes mid (Import ident) =
     [Function OtherFunctionKind $ qualifyWith mid ident]
import2codes mid (ImportTypeWith ident idents) =
     ConstructorName OtherConstrKind (qualifyWith mid ident) :
     map (Function OtherFunctionKind . qualifyWith mid) idents
import2codes mid (ImportTypeAll  ident) =
     [ConstructorName OtherConstrKind $ qualifyWith mid ident]

typeExpr2codes :: TypeExpr -> [Code]
typeExpr2codes (ConstructorType qid tys)
  = TypeConstructor TypeUse qid : concatMap typeExpr2codes tys
typeExpr2codes (VariableType          v) = [Identifier IdOccur (qualify v)]
typeExpr2codes (TupleType           tys) = concatMap typeExpr2codes tys
typeExpr2codes (ListType             ty) = typeExpr2codes ty
typeExpr2codes (ArrowType       ty1 ty2) = concatMap typeExpr2codes [ty1, ty2]
typeExpr2codes (RecordType          _ _) = internalError "SyntaxColoring.typeExpr2codes: Record pattern"
typeExpr2codes (SpecialConstructorType _tcon _tys) = []

showToken :: Token -> [Char]
showToken (Token Id           a) = showAttr a
showToken (Token QId          a) = showAttr a
showToken (Token Sym          a) = showAttr a
showToken (Token QSym         a) = showAttr a
showToken (Token IntTok       a) = showAttr a
showToken (Token FloatTok     a) = showAttr a
showToken (Token CharTok      a) = showAttr a
showToken (Token StringTok    a) = showAttr a
showToken (Token LeftParen    _) = "("
showToken (Token RightParen   _) = ")"
showToken (Token Semicolon    _) = ";"
showToken (Token LeftBrace    _) = "{"
showToken (Token RightBrace   _) = "}"
showToken (Token LeftBracket  _) = "["
showToken (Token RightBracket _) = "]"
showToken (Token Comma        _) = ","
showToken (Token Underscore   _) = "_"
showToken (Token Backquote    _) = "`"
showToken (Token VSemicolon   _) = ""
showToken (Token LeftBraceSemicolon _) = "{;"
showToken (Token VRightBrace  _) = ""
showToken (Token At           _) = "@"
showToken (Token Colon        _) = ":"
showToken (Token DotDot       _) = ".."
showToken (Token DoubleColon  _) = "::"
showToken (Token Equals       _) = "="
showToken (Token Backslash    _) = "\\"
showToken (Token Bar          _) = "|"
showToken (Token LeftArrow    _) = "<-"
showToken (Token RightArrow   _) = "->"
showToken (Token Tilde        _) = "~"
showToken (Token Bind         _) = ":="
showToken (Token Select       _) = ":>"
showToken (Token SymDot       _) = "."
showToken (Token SymMinus     _) = "-"
showToken (Token SymMinusDot  _) = "-."
showToken (Token DoubleArrow  _) = "=>" 
showToken (Token KW_case      _) = "case"
showToken (Token KW_class     _) = "class"
showToken (Token KW_data      _) = "data"
showToken (Token KW_do        _) = "do"
showToken (Token KW_else      _) = "else"
showToken (Token KW_external  _) = "external"
showToken (Token KW_fcase     _) = "fcase"
showToken (Token KW_foreign   _) = "foreign"
showToken (Token KW_free      _) = "free"
showToken (Token KW_if        _) = "if"
showToken (Token KW_import    _) = "import"
showToken (Token KW_in        _) = "in"
showToken (Token KW_infix     _) = "infix"
showToken (Token KW_infixl    _) = "infixl"
showToken (Token KW_infixr    _) = "infixr"
showToken (Token KW_instance  _) = "instance"
showToken (Token KW_let       _) = "let"
showToken (Token KW_module    _) = "module"
showToken (Token KW_newtype   _) = "newtype"
showToken (Token KW_of        _) = "of"
showToken (Token KW_then      _) = "then"
showToken (Token KW_type      _) = "type"
showToken (Token KW_where     _) = "where"
showToken (Token Id_as        _) = "as"
showToken (Token Id_ccall     _) = "ccall"
showToken (Token Id_forall    _) = "forall"
showToken (Token Id_hiding    _) = "hiding"
showToken (Token Id_interface _) = "interface"
showToken (Token Id_interfaceTypeClasses _) = "interfaceTypeClasses"
showToken (Token Id_primitive _) = "primitive"
showToken (Token Id_public    _) = "public"
showToken (Token Id_qualified _) = "qualified"
showToken (Token EOF          _) = ""
showToken (Token LineComment   (StringAttributes sv _)) = sv
showToken (Token LineComment   a                      ) = showAttr a
showToken (Token NestedComment (StringAttributes sv _)) = sv
showToken (Token NestedComment                       a) = showAttr a

showAttr :: Attributes -> [Char]
showAttr NoAttributes            = ""
showAttr (CharAttributes   cv _) = showCharacter cv
showAttr (IntAttributes    iv _) = show iv
showAttr (FloatAttributes  fv _) = show fv
showAttr (StringAttributes sv _) = showSt sv
showAttr (IdentAttributes mid i) = intercalate "." $ mid ++ [i]

showCharacter :: Char -> [Char]
showCharacter c
  | c == '\\'                              = "'\\\\'"
  | c `elem` ('\127' : ['\001' .. '\031']) = show c
  | otherwise                              = ['\'', c, '\'']

showSt :: [Char] -> [Char]
showSt = addQuotes . concatMap toGoodChar
  where addQuotes x = "\"" ++ x ++ "\""

toGoodChar :: Char -> [Char]
toGoodChar c
  | c == '\\'                              = "\\\\"
  | c `elem` ('\127' : ['\001' .. '\031']) = justShow c
  | c == '"'                               = "\\\""
  | otherwise                              = [c]
 where justShow = init . tail . show

{-
codeWithoutUniqueID ::  Code -> String
codeWithoutUniqueID code = maybe (code2string code) (name . unqualify) $ getQualIdent code


codeUnqualify :: Code -> Code
codeUnqualify code = maybe code (setQualIdent code . qualify . unqualify)  $ getQualIdent code
-}

{-
setQualIdent :: Code -> QualIdent -> Code
setQualIdent (Keyword str) _ = (Keyword str)
setQualIdent (Space i) _ = (Space i)
setQualIdent NewLine _ = NewLine
setQualIdent (ConstructorName kind _) qid = (ConstructorName kind qid)
setQualIdent (Function kind _) qid = (Function kind qid)
setQualIdent (ModuleName mid) _ = (ModuleName mid)
setQualIdent (Commentary str) _ = (Commentary str)
setQualIdent (NumberCode str) _ = (NumberCode str)
setQualIdent (Symbol str) _ = (Symbol str)
setQualIdent (Identifier kind _) qid = (Identifier kind qid)
setQualIdent (TypeConstructor kind _) qid = (TypeConstructor kind qid)
setQualIdent (StringCode str) _ = (StringCode str)
setQualIdent (CharCode str) _ = (CharCode str)
-}

-- --- @param Program
-- --- @param line
-- --- @param col
-- --- @return Code at this Position
-- position2code :: Program -> Int -> Int -> Maybe Code
-- position2code []  _ _ = Nothing
-- position2code [_] _ _ = Nothing
-- position2code ((l,c,code):xs@((_,c2,_):_)) lin col
--   | lin == l && col >= c && col < c2 = Just code
--   | l > lin = Nothing
--   | otherwise = position2code xs lin col

-- area2codes :: Program -> Position -> Position -> [Code]
-- area2codes [] _ _ = []
-- area2codes xxs@((l,c,code):xs) p1@Position{file=f} p2
--   | p1 > p2 = area2codes xxs p2 p1
--   | posEnd >= p1 && posBegin <= p2  = code : area2codes xs p1 p2
--   | posBegin > p2 = []
--   | otherwise = area2codes xs p1 p2
--   where
--   posBegin = Position f l c noRef
--   posEnd   = Position f l (c + length (code2string code)) noRef
-- area2codes _ _ _ = internalError "SyntaxColoring.area2codes: no pattern match"