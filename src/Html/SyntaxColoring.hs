{- |
    Module      :  $Header$
    Description :  Split module into code fragments
    Copyright   :  (c)  ??  , someone else
                        2014, Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module arranges the tokens of the module into different code
    categories for HTML presentation. The parsed and typechecked module
    is used to establish links between used identifiers and their definitions.
-}

module Html.SyntaxColoring
  ( Code (..), TypeUsage (..), ConsUsage (..)
  , IdentUsage (..), FuncUsage (..)
  , genProgram, code2string, getQualIdent
  ) where

import Data.Function (on)
import Data.List     (intercalate, sortBy)

import Curry.Base.Ident
import Curry.Base.Position
import Curry.Syntax

import Base.Messages

-- |Type of codes which are distinguished for HTML output
data Code
  = Keyword     String
  | Space       Int
  | NewLine
  | Pragma      String
  | TypeCons    TypeUsage  QualIdent
  | DataCons    ConsUsage  QualIdent
  | Function    FuncUsage  QualIdent
  | Identifier  IdentUsage QualIdent
  | ModuleName  ModuleIdent
  | Commentary  String
  | NumberCode  String
  | StringCode  String
  | CharCode    String
  | Symbol      String
    deriving Show

data TypeUsage
  = TypeDeclare
  | TypeRefer
  | TypeExport
  | TypeImport
    deriving Show

data ConsUsage
  = ConsDeclare
  | ConsPattern
  | ConsCall
  | ConsInfix
  | ConsExport
  | ConsImport
    deriving Show

data FuncUsage
  = FuncDeclare
  | FuncTypeSig
  | FuncCall
  | FuncInfix
  | FuncExport
  | FuncImport
    deriving Show

data IdentUsage
  = IdDeclare -- declare a (type) variable
  | IdRefer   -- refer to a (type) variable
  | IdUnknown -- unknown usage
    deriving Show

-- @param list with parse-Results with descending quality,
--        e.g. [typingParse, fullParse, parse]
-- @param lex-Result
-- @return program
genProgram :: String -> Module -> [(Position, Token)] -> [Code]
genProgram fn m toks = tokenToCodes (first fn) (idsModule m) toks

-- @param code
-- @return qid if available
getQualIdent :: Code -> Maybe QualIdent
getQualIdent (DataCons    _ qid) = Just qid
getQualIdent (Function    _ qid) = Just qid
getQualIdent (Identifier  _ qid) = Just qid
getQualIdent (TypeCons    _ qid) = Just qid
getQualIdent  _                  = Nothing

tokenToCodes :: Position -> [Code] -> [(Position, Token)] -> [Code]
tokenToCodes _      _   []                     = []
tokenToCodes curPos ids toks@((pos, tok) : ts)
  -- advance line
  | line curPos < line pos
  = NewLine         : tokenToCodes (nl curPos) ids toks
  -- advance column
  | column curPos < column pos
  = Space colDiff   : tokenToCodes (incr curPos colDiff) ids toks
  | isPragmaToken tok
  = let (pragmas, (end:rest)) = break (isPragmaEnd . snd) toks
        str = intercalate " " $ map (showToken . snd) (pragmas ++ [end])
    in  Pragma str : tokenToCodes (incr curPos (length str)) ids rest
  -- no identifier token
  | not (isTokenIdentifier tok)
  = tokenToCode tok : tokenToCodes newPos ids ts
  -- identifier, but no more information
  | null ids
  = tokenToCode tok : tokenToCodes newPos ids ts
  | tokenStr == code2string (head ids)
  = head ids        : tokenToCodes newPos (tail ids) ts
  | otherwise
  = tokenToCodes curPos (tail ids) toks
  where
  colDiff  = column pos - column curPos
  tokenStr = showToken tok
  newPos   = incr curPos (length tokenStr)

code2string :: Code -> String
code2string (Keyword         s) = s
code2string (Space           i) = replicate i ' '
code2string NewLine             = "\n"
code2string (Pragma          s) = s
code2string (DataCons    _ qid) = idName $ unqualify qid
code2string (TypeCons    _ qid) = idName $ unqualify qid
code2string (Function    _ qid) = idName $ unqualify qid
code2string (Identifier  _ qid) = idName $ unqualify qid
code2string (ModuleName    mid) = moduleName mid
code2string (Commentary      s) = s
code2string (NumberCode      s) = s
code2string (StringCode      s) = s
code2string (CharCode        s) = s
code2string (Symbol          s) = s

tokenToCode :: Token -> Code
tokenToCode tok@(Token cat _)
  | cat `elem` numCategories          = NumberCode (showToken tok)
  | cat == CharTok                    = CharCode   (showToken tok)
  | cat == StringTok                  = StringCode (showToken tok)
  | cat `elem` keywordCategories      = Keyword    (showToken tok)
  | cat `elem` specialIdentCategories = Keyword    (showToken tok)
  | cat `elem` punctuationCategories  = Symbol     (showToken tok)
  | cat `elem` reservedOpsCategories  = Symbol     (showToken tok)
  | cat `elem` commentCategories      = Commentary (showToken tok)
  | cat `elem` identCategories        = Identifier IdUnknown $ qualify $ mkIdent
                                      $ showToken tok
  | cat `elem` whiteSpaceCategories   = Space 0
  | cat `elem` pragmaCategories       = Pragma     (showToken tok)
  | otherwise                         = internalError $
    "SyntaxColoring.tokenToCode: Unknown token" ++ showToken tok

numCategories :: [Category]
numCategories = [IntTok, FloatTok]

keywordCategories :: [Category]
keywordCategories =
  [ KW_case, KW_data, KW_do, KW_else, KW_external, KW_fcase, KW_foreign
  , KW_free, KW_if, KW_import, KW_in, KW_infix, KW_infixl, KW_infixr
  , KW_let, KW_module, KW_newtype, KW_of, KW_then, KW_type, KW_where
  ]

specialIdentCategories :: [Category]
specialIdentCategories =
  [ Id_as, Id_ccall, Id_forall, Id_hiding
  , Id_interface, Id_primitive, Id_qualified ]

punctuationCategories :: [Category]
punctuationCategories =
  [ LeftParen, RightParen, Semicolon, LeftBrace, RightBrace
  , LeftBracket, RightBracket, Comma, Underscore, Backquote ]

reservedOpsCategories :: [Category]
reservedOpsCategories =
  [ At, Colon, DotDot, DoubleColon, Equals, Backslash, Bar
  , LeftArrow, RightArrow, Tilde, Bind, Select ]

commentCategories :: [Category]
commentCategories = [LineComment, NestedComment]

identCategories :: [Category]
identCategories = [Id, QId, Sym, QSym, SymDot, SymMinus, SymMinusDot]

isPragmaToken :: Token -> Bool
isPragmaToken (Token cat _) = cat `elem` pragmaCategories

isPragmaEnd :: Token -> Bool
isPragmaEnd (Token cat _) = cat == PragmaEnd

isTokenIdentifier :: Token -> Bool
isTokenIdentifier (Token cat _) = cat `elem` identCategories

whiteSpaceCategories :: [Category]
whiteSpaceCategories = [EOF, VSemicolon, VRightBrace]

pragmaCategories :: [Category]
pragmaCategories = [PragmaLanguage, PragmaOptions, PragmaEnd]

-- DECL Position

declPos :: Decl -> Position
declPos (InfixDecl        p _ _ _  ) = p
declPos (DataDecl         p _ _ _  ) = p
declPos (NewtypeDecl      p _ _ _  ) = p
declPos (TypeDecl         p _ _ _  ) = p
declPos (TypeSig          p _ _    ) = p
declPos (FunctionDecl     p _ _    ) = p
declPos (ForeignDecl      p _ _ _ _) = p
declPos (ExternalDecl     p _      ) = p
declPos (PatternDecl      p _ _    ) = p
declPos (FreeDecl         p _      ) = p

cmpDecl :: Decl -> Decl -> Ordering
cmpDecl = compare `on` declPos

cmpImportDecl :: ImportDecl -> ImportDecl -> Ordering
cmpImportDecl = compare `on` (\ (ImportDecl p _ _ _ _) -> p)

-- -----------------------------------------------------------------------------
-- Extract all identifiers mentioned in the source code as a Code entity
-- in the order of their occurrence. The extracted information is then used
-- to enrich the identifier tokens with additional information, e.g., for
-- link generation.
-- -----------------------------------------------------------------------------

idsModule :: Module -> [Code]
idsModule (Module _ mid es is ds) =
  let hdrCodes = ModuleName mid : idsExportSpec es
      impCodes = concatMap idsImportDecl (sortBy cmpImportDecl is)
      dclCodes = concatMap idsDecl       (sortBy cmpDecl ds)
  in  map (addModuleIdent mid) $ hdrCodes ++ impCodes ++ dclCodes

addModuleIdent :: ModuleIdent -> Code -> Code
addModuleIdent mid c@(Function x qid)
  | hasGlobalScope (unqualify qid) = Function x (qualQualify mid qid)
  | otherwise                      = c
addModuleIdent mid cn@(DataCons x qid)
  | not $ isQualified qid          = DataCons x (qualQualify mid qid)
  | otherwise                      = cn
addModuleIdent mid tc@(TypeCons x qid)
  | not $ isQualified qid          = TypeCons x (qualQualify mid qid)
  | otherwise                      = tc
addModuleIdent _   c               = c

-- Exports

idsExportSpec ::  Maybe ExportSpec -> [Code]
idsExportSpec Nothing                 = []
idsExportSpec (Just (Exporting _ es)) = concatMap idsExport es

idsExport :: Export -> [Code]
idsExport (Export            qid) = [Function FuncExport qid]
idsExport (ExportTypeWith qid cs) = TypeCons TypeExport qid :
  map (DataCons ConsExport . qualify) cs
idsExport (ExportTypeAll     qid) = [TypeCons TypeExport qid]
idsExport (ExportModule      mid) = [ModuleName mid]

-- Imports

idsImportDecl :: ImportDecl -> [Code]
idsImportDecl (ImportDecl _ mid _ mAlias spec)
  = ModuleName mid : aliasCode ++ maybe [] (idsImportSpec mid) spec
  where aliasCode = maybe [] ((:[]) . ModuleName) mAlias

idsImportSpec :: ModuleIdent -> ImportSpec -> [Code]
idsImportSpec mid (Importing _ is) = concatMap (idsImport mid) is
idsImportSpec mid (Hiding    _ is) = concatMap (idsImport mid) is

idsImport :: ModuleIdent -> Import -> [Code]
idsImport mid (Import            i) =
  [Function FuncImport $ qualifyWith mid i]
idsImport mid (ImportTypeWith t cs) =
  TypeCons TypeImport (qualifyWith mid t) :
    map (DataCons ConsImport . qualifyWith mid) cs
idsImport mid (ImportTypeAll     t) =
  [TypeCons TypeImport $ qualifyWith mid t]

-- Declarations

idsDecl :: Decl -> [Code]
idsDecl (InfixDecl _   _ _ ops) = map (Function FuncInfix . qualify) ops
idsDecl (DataDecl   _ d vs cds) = TypeCons TypeDeclare (qualify d)
                                    :  map (Identifier IdDeclare . qualify) vs
                                    ++ concatMap idsConstrDecl cds
idsDecl (NewtypeDecl _ t vs nc) = TypeCons TypeDeclare (qualify t)
                                    :  map (Identifier IdDeclare . qualify) vs
                                    ++ idsNewConstrDecl nc
idsDecl (TypeDecl    _ t vs ty) = TypeCons TypeDeclare (qualify t)
                                    :  map (Identifier IdDeclare . qualify) vs
                                    ++ idsTypeExpr ty
idsDecl (TypeSig       _ fs ty) = map (Function FuncTypeSig . qualify) fs
                                    ++ idsTypeExpr ty
idsDecl (FunctionDecl  _ _ eqs) = concatMap idsEquation eqs
idsDecl (ForeignDecl _ _ _ _ _) = []
idsDecl (ExternalDecl     _ fs) = map (Function FuncDeclare . qualify) fs
idsDecl (PatternDecl   _ p rhs) = idsPat p ++ idsRhs rhs
idsDecl (FreeDecl         _ vs) = map (Identifier IdDeclare . qualify) vs

idsConstrDecl :: ConstrDecl -> [Code]
idsConstrDecl (ConstrDecl     _ _ c tys)
  = DataCons ConsDeclare (qualify c) : concatMap idsTypeExpr tys
idsConstrDecl (ConOpDecl _ _ ty1 op ty2)
  = idsTypeExpr ty1 ++ (DataCons ConsDeclare $ qualify op) : idsTypeExpr ty2
idsConstrDecl (RecordDecl _ _ c fs)
  = DataCons ConsDeclare (qualify c) : concatMap idsFieldDecl fs

idsNewConstrDecl :: NewConstrDecl -> [Code]
idsNewConstrDecl (NewConstrDecl _ _ c ty)
  = DataCons ConsDeclare (qualify c) : idsTypeExpr ty
idsNewConstrDecl (NewRecordDecl _ _ c (l,ty))
  = DataCons ConsDeclare (qualify c) : (Function FuncDeclare $ qualify l)
  : idsTypeExpr ty

idsTypeExpr :: TypeExpr -> [Code]
idsTypeExpr (ConstructorType qid tys) = TypeCons TypeRefer qid :
                                           concatMap idsTypeExpr tys
idsTypeExpr (VariableType          v) = [Identifier IdRefer (qualify v)]
idsTypeExpr (TupleType           tys) = concatMap idsTypeExpr tys
idsTypeExpr (ListType             ty) = idsTypeExpr ty
idsTypeExpr (ArrowType       ty1 ty2) = concatMap idsTypeExpr [ty1, ty2]
idsTypeExpr (ParenType            ty) = idsTypeExpr ty

idsFieldDecl :: FieldDecl -> [Code]
idsFieldDecl (FieldDecl _ ls ty) =
  map (Function FuncDeclare . qualify . unRenameIdent) ls ++ idsTypeExpr ty

idsEquation :: Equation -> [Code]
idsEquation (Equation _ lhs rhs) = idsLhs lhs ++ idsRhs rhs

idsLhs :: Lhs -> [Code]
idsLhs (FunLhs    f ps) = Function FuncDeclare (qualify f) : concatMap idsPat ps
idsLhs (OpLhs p1 op p2) = idsPat p1 ++ [Function FuncDeclare $ qualify op]
                                    ++ idsPat p2
idsLhs (ApLhs   lhs ps) = idsLhs lhs ++ concatMap idsPat ps

idsRhs :: Rhs -> [Code]
idsRhs (SimpleRhs _ e ds) = idsExpr e ++ concatMap idsDecl ds
idsRhs (GuardedRhs ce ds) = concatMap idsCondExpr ce ++ concatMap idsDecl ds

idsCondExpr :: CondExpr -> [Code]
idsCondExpr (CondExpr _ e1 e2) = idsExpr e1 ++ idsExpr e2

idsPat :: Pattern -> [Code]
idsPat (LiteralPattern          _) = []
idsPat (NegativePattern       _ _) = []
idsPat (VariablePattern         v) = [Identifier IdDeclare (qualify v)]
idsPat (ConstructorPattern qid ps) = DataCons ConsPattern qid
                                      : concatMap idsPat ps
idsPat (InfixPattern    p1 qid p2) = idsPat p1 ++
                                       DataCons ConsPattern qid : idsPat p2
idsPat (ParenPattern            p) = idsPat p
idsPat (RecordPattern      qid fs) = DataCons ConsPattern qid
                                      : concatMap (idsField idsPat) fs
idsPat (TuplePattern         _ ps) = concatMap idsPat ps
idsPat (ListPattern          _ ps) = concatMap idsPat ps
idsPat (AsPattern             v p) = Identifier IdDeclare (qualify v) : idsPat p
idsPat (LazyPattern           _ p) = idsPat p
idsPat (FunctionPattern    qid ps) = Function FuncCall qid
                                      : concatMap idsPat ps
idsPat (InfixFuncPattern  p1 f p2) = idsPat p1 ++
                                      Function FuncInfix f : idsPat p2

idsExpr :: Expression -> [Code]
idsExpr (Literal                _) = []
idsExpr (Variable             qid)
  | isQualified qid                = [Function FuncCall qid]
  | hasGlobalScope (unqualify qid) = [Function FuncCall qid]
  | otherwise                      = [Identifier IdRefer qid]
idsExpr (Constructor          qid) = [DataCons ConsCall qid]
idsExpr (Paren                  e) = idsExpr e
idsExpr (Typed               e ty) = idsExpr e ++ idsTypeExpr ty
idsExpr (Record            qid fs) = DataCons ConsCall qid
                                      : concatMap (idsField idsExpr) fs
idsExpr (RecordUpdate        e fs) = idsExpr e
                                      ++ concatMap (idsField idsExpr) fs
idsExpr (Tuple               _ es) = concatMap idsExpr es
idsExpr (List                _ es) = concatMap idsExpr es
idsExpr (ListCompr      _ e stmts) = idsExpr e ++ concatMap idsStmt stmts
idsExpr (EnumFrom               e) = idsExpr e
idsExpr (EnumFromThen       e1 e2) = concatMap idsExpr [e1, e2]
idsExpr (EnumFromTo         e1 e2) = concatMap idsExpr [e1, e2]
idsExpr (EnumFromThenTo  e1 e2 e3) = concatMap idsExpr [e1, e2, e3]
idsExpr (UnaryMinus       ident e) = Symbol (idName ident) : idsExpr e
idsExpr (Apply              e1 e2) = idsExpr e1 ++ idsExpr e2
idsExpr (InfixApply      e1 op e2) = idsExpr e1 ++ idsInfix op ++ idsExpr e2
idsExpr (LeftSection         e op) = idsExpr e ++ idsInfix op
idsExpr (RightSection        op e) = idsInfix op ++ idsExpr e
idsExpr (Lambda            _ ps e) = concatMap idsPat ps ++ idsExpr e
idsExpr (Let                 ds e) = concatMap idsDecl ds ++ idsExpr e
idsExpr (Do               stmts e) = concatMap idsStmt stmts ++ idsExpr e
idsExpr (IfThenElse    _ e1 e2 e3) = concatMap idsExpr [e1, e2, e3]
idsExpr (Case          _ _ e alts) = idsExpr e ++ concatMap idsAlt alts

idsField :: (a -> [Code]) -> Field a -> [Code]
idsField f (Field _ l x) = Function FuncCall l : f x

idsInfix :: InfixOp -> [Code]
idsInfix (InfixOp     qid) = [Function FuncInfix qid]
idsInfix (InfixConstr qid) = [DataCons ConsInfix qid]

idsStmt :: Statement -> [Code]
idsStmt (StmtExpr   _ e) = idsExpr e
idsStmt (StmtDecl    ds) = concatMap idsDecl ds
idsStmt (StmtBind _ p e) = idsPat p ++ idsExpr e

idsAlt :: Alt -> [Code]
idsAlt (Alt _ p rhs) = idsPat p ++ idsRhs rhs

-- -----------------------------------------------------------------------------
-- Conversion from a token to a string
-- -----------------------------------------------------------------------------

showToken :: Token -> String
showToken (Token Id                 a) = showAttr a
showToken (Token QId                a) = showAttr a
showToken (Token Sym                a) = showAttr a
showToken (Token QSym               a) = showAttr a
showToken (Token IntTok             a) = showAttr a
showToken (Token FloatTok           a) = showAttr a
showToken (Token CharTok            a) = showAttr a
showToken (Token StringTok          a) = showAttr a
showToken (Token LeftParen          _) = "("
showToken (Token RightParen         _) = ")"
showToken (Token Semicolon          _) = ";"
showToken (Token LeftBrace          _) = "{"
showToken (Token RightBrace         _) = "}"
showToken (Token LeftBracket        _) = "["
showToken (Token RightBracket       _) = "]"
showToken (Token Comma              _) = ","
showToken (Token Underscore         _) = "_"
showToken (Token Backquote          _) = "`"
showToken (Token VSemicolon         _) = ""
showToken (Token VRightBrace        _) = ""
showToken (Token At                 _) = "@"
showToken (Token Colon              _) = ":"
showToken (Token DotDot             _) = ".."
showToken (Token DoubleColon        _) = "::"
showToken (Token Equals             _) = "="
showToken (Token Backslash          _) = "\\"
showToken (Token Bar                _) = "|"
showToken (Token LeftArrow          _) = "<-"
showToken (Token RightArrow         _) = "->"
showToken (Token Tilde              _) = "~"
showToken (Token Bind               _) = ":="
showToken (Token Select             _) = ":>"
showToken (Token SymDot             _) = "."
showToken (Token SymMinus           _) = "-"
showToken (Token SymMinusDot        _) = "-."
showToken (Token KW_case            _) = "case"
showToken (Token KW_data            _) = "data"
showToken (Token KW_do              _) = "do"
showToken (Token KW_else            _) = "else"
showToken (Token KW_external        _) = "external"
showToken (Token KW_fcase           _) = "fcase"
showToken (Token KW_foreign         _) = "foreign"
showToken (Token KW_free            _) = "free"
showToken (Token KW_if              _) = "if"
showToken (Token KW_import          _) = "import"
showToken (Token KW_in              _) = "in"
showToken (Token KW_infix           _) = "infix"
showToken (Token KW_infixl          _) = "infixl"
showToken (Token KW_infixr          _) = "infixr"
showToken (Token KW_let             _) = "let"
showToken (Token KW_module          _) = "module"
showToken (Token KW_newtype         _) = "newtype"
showToken (Token KW_of              _) = "of"
showToken (Token KW_then            _) = "then"
showToken (Token KW_type            _) = "type"
showToken (Token KW_where           _) = "where"
showToken (Token Id_as              _) = "as"
showToken (Token Id_ccall           _) = "ccall"
showToken (Token Id_forall          _) = "forall"
showToken (Token Id_hiding          _) = "hiding"
showToken (Token Id_interface       _) = "interface"
showToken (Token Id_primitive       _) = "primitive"
showToken (Token Id_qualified       _) = "qualified"
showToken (Token EOF                _) = ""
showToken (Token PragmaHiding       _) = "{-# HIDING"
showToken (Token PragmaLanguage     _) = "{-# LANGUAGE"
showToken (Token PragmaOptions      a) = "{-# OPTIONS" ++ showAttr a
showToken (Token PragmaEnd          _) = "#-}"
showToken (Token LineComment   (StringAttributes s _)) = s
showToken (Token LineComment   a                     ) = showAttr a
showToken (Token NestedComment (StringAttributes s _)) = s
showToken (Token NestedComment                      a) = showAttr a

showAttr :: Attributes -> [Char]
showAttr NoAttributes             = ""
showAttr (CharAttributes     c _) = show c
showAttr (IntAttributes      i _) = show i
showAttr (FloatAttributes    f _) = show f
showAttr (StringAttributes   s _) = show s
showAttr (IdentAttributes    m i)
  | null m    = show $ qualify                  (mkIdent i)
  | otherwise = show $ qualifyWith (mkMIdent m) (mkIdent i)
showAttr (OptionsAttributes mt s) = showTool mt ++ ' ' : s

showTool :: Maybe String -> String
showTool Nothing  = ""
showTool (Just t) = '_' : t
