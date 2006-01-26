module SyntaxColoring where


--(module SyntaxColoring, parseString,main) where

import System.Environment
import CurryLexer
import Position
import Error
import Frontend
import Ident
import CurrySyntax 
import Char
import Maybe
import List


main = getArgs >>= test . head

test s = filename2program s >>= writeFile ("out/" ++ basename s ++ ".html") . program2html      
     


data Program = Program [Code] String  deriving Show

data Code =  Keyword String
           | Space Int
           | NewLine
           | ConstructorName String
           | TypeConstructor String
           | Function String
           | ModuleName String
           | Commentary String
           | Literale String
           | Symbol String
           | Identifier String deriving Show
           
data Color = Blue
            |Green
            |Black
            |Red
            |White
            |Purple
            |Aqua
            |Maroon
            |Fuchsia
            |Silver

catIdentifiers :: Module -> [Code]
catIdentifiers  (Module  moduleIdent maybeExportSpec decls) =
    (moduleIdent2codes moduleIdent ++
     (if isJust maybeExportSpec 
           then exportSpec2codes (fromJust maybeExportSpec) 
           else []) ++
     (concatMap decl2codes decls))
     
genCode :: Module -> [(Position,Token)] -> [Code]
genCode modul posNtokList =
    tokenNcodes2codes 1 1 posNtokList (catIdentifiers modul)
            
filename2program :: String -> IO Program
filename2program filename =
     readFile filename >>= \ cont ->
     let (Result _ m) = (parse filename cont)
         (Result _ ls) = (Frontend.lex filename cont) in    
     return (genProgram m ls)    
                        
genProgram :: Module -> [(Position,Token)] -> Program
genProgram  modul posNtokList = 
      Program (genCode modul posNtokList)
              ""      
            
             

tokenNcodes2codes :: Int -> Int -> [(Position,Token)] -> [Code] -> [Code]
tokenNcodes2codes _ _ [] _ = []          
tokenNcodes2codes currLine currCol toks@((Position _ line col,token):ts) codes 
    | currLine < line = 
           replicate (line - currLine) NewLine ++
           tokenNcodes2codes line 1 toks codes
    | currCol < col =  
           Space (col - currCol) :         
           tokenNcodes2codes currLine col toks codes
    | isTokenIdentifier token && null codes =
           error ("empty Code-List, Token: " ++ show token)
    | not (isTokenIdentifier token) =
           token2code token : tokenNcodes2codes newLine newCol ts codes
    | tokenStr == code2string (head codes) =
           (head codes) : tokenNcodes2codes newLine newCol ts (tail codes)       
    | otherwise = 
           tokenNcodes2codes currLine currCol toks (tail codes)
  where
      tokenStr = token2string token            
      newLine   = (currLine + length (lines tokenStr)) - 1 
      newCol  = currCol + length tokenStr    
           

            

                
code2color (Keyword _) = Blue
code2color (Space _)= White
code2color NewLine = White
code2color (ConstructorName _) = Fuchsia
code2color (Function _) = Purple
code2color (ModuleName _) = Maroon
code2color (Commentary _) = Green
code2color (Literale _) = Black
code2color (Symbol _) = Silver
code2color (Identifier _) = Black
code2color (TypeConstructor _) = Blue
                  
code2string (Keyword str) = str
code2string (Space i)= concat (replicate i " ")
code2string NewLine = "\n"
code2string (ConstructorName str) = str
code2string (Function str) = str
code2string (ModuleName str) = str
code2string (Commentary str) = str
code2string (Literale str) = str
code2string (Symbol str) = str
code2string (Identifier str) = str                      
code2string (TypeConstructor str) = str                                  


color2html Blue = "blue"
color2html Green = "green"
color2html Black = "black"
color2html Red = "red"
color2html White = "white"     
color2html Purple = "#800080"
color2html Aqua = "#00FFFF"
color2html Maroon = "#800000"
color2html Fuchsia = "#FF00FF"  
color2html Silver = "#C0C0C0"

token2code :: Token -> Code
token2code tok@(Token cat _)
    | elem cat [CharTok,IntTok,FloatTok,IntegerTok,StringTok]
         = Literale (token2string tok)
    | elem cat [KW_case,KW_choice,KW_data,KW_do,KW_else,KW_eval,KW_external,
                KW_free,KW_if,KW_import,KW_in,KW_infix,KW_infixl,KW_infixr,
                KW_let,KW_module,KW_newtype,KW_of,KW_rigid,KW_then,KW_type,
                KW_where,Id_as,Id_ccall,Id_forall,Id_hiding,Id_interface,Id_primitive]
         =  Keyword (token2string tok)
    | elem cat [LeftParen,RightParen,Semicolon,LeftBrace,RightBrace,LeftBracket,
                RightBracket,Comma,Underscore,Backquote,VSemicolon,VRightBrace,
                At,Colon,DotDot,DoubleColon,Equals,Backslash,Bar,LeftArrow,RightArrow,
                Tilde,Sym_Dot,Sym_Minus,Sym_MinusDot]
         = Symbol (token2string tok)
    | elem cat [LineComment, NestedComment]
         = Commentary (token2string tok)
    | elem cat [Id_qualified,Id,QId,Sym,QSym]
         = Identifier (token2string tok)
    | cat == EOF = Space 0 
    
isTokenIdentifier :: Token -> Bool
isTokenIdentifier (Token cat _) = elem cat [Id_qualified,Id,QId,Sym,QSym]
    
               

               
program2html (Program codes unparsed) =
    "<HTML><HEAD></HEAD><BODY style=\"font-family:'Courier New', Arial;\">" ++
    concat (map code2html codes ++ [unparsed2html unparsed]) ++
    "</BODY></HTML>"
 

code2html c = spanTag (color2html (code2color c)) 
                      (replace ' ' 
                               "&nbsp;" 
                               (replace '\n' 
                                        "<br>\n" 
                                        (code2string c)))

spanTag :: String -> String -> String
spanTag color str = "<SPAN style=\"color:"++ color ++"\">" ++ str ++ "</SPAN>"

unparsed2html str = spanTag "red" $ replace ' ' "&nbsp;" $ replace '\n' "<br>\n" str

replace :: Char -> String -> String -> String
replace old new = foldr (\ x -> if x == old then (new ++) else ([x]++)) ""

-- DECL TO CODE -------------------------------------------------------------------- 

exportSpec2codes :: ExportSpec -> [Code]
exportSpec2codes (Exporting _ exports) = concatMap export2codes exports

export2codes :: Export -> [Code]
export2codes (Export qualIdent) =
     qualIdent2codes Function qualIdent  
export2codes (ExportTypeWith qualIdent idents) = 
     qualIdent2codes ConstructorName qualIdent ++ map (Function . name) idents
export2codes (ExportTypeAll  qualIdent) = 
     qualIdent2codes ConstructorName qualIdent  
export2codes (ExportModule moduleIdent) = 
     moduleIdent2codes moduleIdent

decl2codes :: Decl -> [Code]            
decl2codes (ImportDecl _ moduleIdent xQualified xModuleIdent importSpec) = 
     moduleIdent2codes moduleIdent ++
     maybe [] importSpec2codes  importSpec
decl2codes (InfixDecl _ _ _ idents) =
     (map (Function . name) idents)
decl2codes (DataDecl _ ident idents constrDecls) =
     [TypeConstructor (name ident)] ++ 
     map (Identifier . name) idents ++
     concatMap constrDecl2codes constrDecls
decl2codes (NewtypeDecl xPosition xIdent yIdents xNewConstrDecl) =
     []
decl2codes (TypeDecl _ ident idents typeExpr) =
     TypeConstructor (name ident) : 
     map (Identifier . name) idents ++ 
     typeExpr2codes typeExpr
decl2codes (TypeSig _ idents typeExpr) =
     map (Function . name) idents ++ typeExpr2codes typeExpr
decl2codes (EvalAnnot xPosition xIdents xEvalAnnotation) =
     []
decl2codes (FunctionDecl _ ident equations) =
     Function (name ident) : concatMap equation2codes equations
decl2codes (ExternalDecl xPosition xCallConv xString xIdent xTypeExpr) =
     []
decl2codes (FlatExternalDecl _ idents) =
     map (Function . name) idents
decl2codes (PatternDecl xPosition constrTerm rhs) =
     constrTerm2codes constrTerm ++ rhs2codes rhs
decl2codes (ExtraVariables _ idents) =
     map (Identifier . name) idents
  
equation2codes :: Equation -> [Code]
equation2codes (Equation _ lhs rhs) =
     lhs2codes lhs ++ rhs2codes rhs
     
lhs2codes :: Lhs -> [Code]
lhs2codes (FunLhs ident constrTerms) =
    (Function $ name ident) : concatMap constrTerm2codes constrTerms
lhs2codes (OpLhs constrTerm1 ident constrTerm2) =
    constrTerm2codes constrTerm1 ++ [Function $ name ident] ++ constrTerm2codes constrTerm2
lhs2codes (ApLhs lhs constrTerms) =
    lhs2codes lhs ++ concatMap constrTerm2codes constrTerms     

rhs2codes :: Rhs -> [Code]
rhs2codes (SimpleRhs _ expression decls) =
    expression2codes expression ++ concatMap decl2codes decls
rhs2codes (GuardedRhs condExprs decls) =
    concatMap condExpr2codes condExprs ++ concatMap decl2codes decls
    
condExpr2codes :: CondExpr -> [Code]
condExpr2codes (CondExpr _ expression1 expression2) =   
   expression2codes expression1 ++ expression2codes expression2    
    
constrTerm2codes :: ConstrTerm -> [Code]
constrTerm2codes (LiteralPattern literal) = []
constrTerm2codes (NegativePattern ident literal) = []
constrTerm2codes (VariablePattern ident) = [Identifier (name ident)]
constrTerm2codes (ConstructorPattern qualIdent constrTerms) =
    qualIdent2codes ConstructorName qualIdent ++ concatMap constrTerm2codes constrTerms
constrTerm2codes (InfixPattern constrTerm1 qualIdent constrTerm2) =
    constrTerm2codes constrTerm1 ++ qualIdent2codes ConstructorName qualIdent ++ constrTerm2codes constrTerm2
constrTerm2codes (ParenPattern constrTerm) = constrTerm2codes constrTerm
constrTerm2codes (TuplePattern constrTerms) = concatMap constrTerm2codes constrTerms
constrTerm2codes (ListPattern constrTerms) = concatMap constrTerm2codes constrTerms
constrTerm2codes (AsPattern ident constrTerm) =
    (Function $ name ident) : constrTerm2codes constrTerm
constrTerm2codes (LazyPattern constrTerm) = constrTerm2codes constrTerm
constrTerm2codes (FunctionPattern qualIdent constrTerms) = 
    qualIdent2codes Function qualIdent ++ concatMap constrTerm2codes constrTerms
constrTerm2codes (InfixFuncPattern constrTerm1 qualIdent constrTerm2) =
    constrTerm2codes constrTerm1 ++ qualIdent2codes Function qualIdent ++ constrTerm2codes constrTerm2
   
expression2codes :: Expression -> [Code]
expression2codes (Literal literal) = []
expression2codes (Variable qualIdent) = 
    qualIdent2codes Identifier   qualIdent
expression2codes (Constructor qualIdent) = 
    qualIdent2codes ConstructorName qualIdent
expression2codes (Paren expression) = 
    expression2codes expression
expression2codes (Typed expression typeExpr) = 
    expression2codes expression ++ typeExpr2codes typeExpr
expression2codes (Tuple expressions) = 
    concatMap expression2codes expressions
expression2codes (List expressions) = 
    concatMap expression2codes expressions
expression2codes (ListCompr expression statements) = 
    expression2codes expression ++ concatMap statement2codes statements
expression2codes (EnumFrom expression) = 
    expression2codes expression
expression2codes (EnumFromThen expression1 expression2) = 
    expression2codes expression1 ++ expression2codes expression2
expression2codes (EnumFromTo expression1 expression2) = 
    expression2codes expression1 ++ expression2codes expression2
expression2codes (EnumFromThenTo expression1 expression2 expression3) = 
    expression2codes expression1 ++ 
    expression2codes expression2 ++ 
    expression2codes expression3
expression2codes (UnaryMinus ident expression) = 
    [] ++ expression2codes expression
expression2codes (Apply expression1 expression2) = 
    expression2codes expression1 ++ expression2codes expression2
expression2codes (InfixApply expression1 infixOp expression2) = 
    expression2codes expression1 ++ infixOp2codes infixOp ++ expression2codes expression2
expression2codes (LeftSection expression infixOp) = 
    expression2codes expression ++ infixOp2codes infixOp
expression2codes (RightSection infixOp expression) = 
    infixOp2codes infixOp ++ expression2codes expression
expression2codes (Lambda constrTerms expression) = 
    concatMap constrTerm2codes constrTerms ++ expression2codes expression
expression2codes (Let decls expression) = 
    concatMap decl2codes decls ++ expression2codes expression
expression2codes (Do statements expression) = 
    concatMap statement2codes statements ++ expression2codes expression
expression2codes (IfThenElse expression1 expression2 expression3) = 
    expression2codes expression1 ++ expression2codes expression2 ++ expression2codes expression3
expression2codes (Case expression alts) = 
    expression2codes expression ++ concatMap alt2codes alts
    
infixOp2codes :: InfixOp -> [Code]
infixOp2codes (InfixOp qualIdent) = qualIdent2codes Function qualIdent
infixOp2codes (InfixConstr qualIdent) = qualIdent2codes ConstructorName qualIdent


statement2codes :: Statement -> [Code] 
statement2codes (StmtExpr expression) =
    expression2codes expression
statement2codes (StmtDecl decls) =
    concatMap decl2codes decls
statement2codes (StmtBind constrTerm expression) =
     constrTerm2codes constrTerm ++ expression2codes expression


alt2codes :: Alt -> [Code]
alt2codes (Alt _ constrTerm rhs) =
    constrTerm2codes constrTerm ++ rhs2codes rhs
         
constrDecl2codes :: ConstrDecl -> [Code]
constrDecl2codes (ConstrDecl _ idents ident typeExprs) =
    (ConstructorName $ name ident) : concatMap typeExpr2codes typeExprs
constrDecl2codes (ConOpDecl _ idents typeExpr1 ident typeExpr2) =   
    typeExpr2codes typeExpr1 ++ [ConstructorName $ name ident] ++ typeExpr2codes typeExpr2

moduleIdent2codes :: ModuleIdent -> [Code]     
moduleIdent2codes = map ModuleName . moduleQualifiers
          
importSpec2codes :: ImportSpec -> [Code]
importSpec2codes (Importing _ imports) = concatMap import2codes imports
importSpec2codes (Hiding _ imports) = concatMap import2codes imports

import2codes :: Import -> [Code]
import2codes (Import ident) =
     [Function $ name ident]  
import2codes (ImportTypeWith ident idents) = 
     [ConstructorName $ name ident] ++ map (Function . name) idents
import2codes (ImportTypeAll  ident) = 
     [ConstructorName $ name ident]  
     
typeExpr2codes :: TypeExpr -> [Code]     
typeExpr2codes (ConstructorType qualIdent typeExprs) = 
    qualIdent2codes TypeConstructor qualIdent ++ concatMap typeExpr2codes typeExprs
typeExpr2codes (VariableType ident) = 
    [TypeConstructor $ name ident]
typeExpr2codes (TupleType typeExprs) = 
    concatMap typeExpr2codes typeExprs
typeExpr2codes (ListType typeExpr) = 
    typeExpr2codes typeExpr
typeExpr2codes (ArrowType typeExpr1 typeExpr2) = 
    typeExpr2codes typeExpr1 ++ typeExpr2codes typeExpr2

qualIdent2codes :: (String -> Code) -> QualIdent -> [Code]
qualIdent2codes  toCode qualIdent = helper $ splitQualIdent qualIdent
   where
      helper (Nothing,ident) = [toCode $ name ident]
      helper (Just moduleIdent,ident) = moduleIdent2codes moduleIdent ++ [toCode $ name ident]



-- TOKEN TO STRING ------------------------------------------------------------

token2string (Token Id a) = attributes2string a
token2string (Token QId a) = attributes2string a
token2string (Token Sym a) = attributes2string a
token2string (Token QSym a) = attributes2string a
token2string (Token IntTok a) = attributes2string a
token2string (Token FloatTok a) = attributes2string a
token2string (Token CharTok a) = attributes2string a
token2string (Token IntegerTok a) = attributes2string a
token2string (Token StringTok a) = attributes2string a
token2string (Token LeftParen _) = "("
token2string (Token RightParen _) = ")"
token2string (Token Semicolon _) = ";"
token2string (Token LeftBrace _) = "{"
token2string (Token RightBrace _) = "}"
token2string (Token LeftBracket _) = "["
token2string (Token RightBracket _) = "]"
token2string (Token Comma _) = ","
token2string (Token Underscore _) = "_"
token2string (Token Backquote _) = "`"
token2string (Token VSemicolon _) = ";"
token2string (Token VRightBrace _) = "}"
token2string (Token At _) = "@"
token2string (Token Colon _) = ":"
token2string (Token DotDot _) = ".."
token2string (Token DoubleColon _) = "::"
token2string (Token Equals _) = "="
token2string (Token Backslash _) = "\\"
token2string (Token Bar _) = "|"
token2string (Token LeftArrow _) = "<-"
token2string (Token RightArrow _) = "->"
token2string (Token Tilde _) = "~"
token2string (Token Sym_Dot _) = "."
token2string (Token Sym_Minus _) = "-"
token2string (Token Sym_MinusDot _) = "-."
token2string (Token KW_case _) = "case"
token2string (Token KW_choice _) = "choice"
token2string (Token KW_data _) = "data"
token2string (Token KW_do _) = "do"
token2string (Token KW_else _) = "else"
token2string (Token KW_eval _) = "eval"
token2string (Token KW_external _) = "external"
token2string (Token KW_free _) = "free"
token2string (Token KW_if _) = "if"
token2string (Token KW_import _) = "import"
token2string (Token KW_in _) = "in"
token2string (Token KW_infix _) = "infix"
token2string (Token KW_infixl _) = "infixl"
token2string (Token KW_infixr _) = "infixr"
token2string (Token KW_let _) = "let"
token2string (Token KW_module _) = "module"
token2string (Token KW_newtype _) = "newtype"
token2string (Token KW_of _) = "of"
token2string (Token KW_rigid _) = "rigid"
token2string (Token KW_then _) = "then"
token2string (Token KW_type _) = "type"
token2string (Token KW_where _) = "where"
token2string (Token Id_as _) = "as"
token2string (Token Id_ccall _) = "ccall"
token2string (Token Id_forall _) = "forall"
token2string (Token Id_hiding _) = "hiding"
token2string (Token Id_interface _) = "interface"
token2string (Token Id_primitive _) = "primitive"
token2string (Token Id_qualified _) = "qualified"
token2string (Token EOF _) = ""
token2string (Token LineComment (StringAttributes sval _)) = sval
token2string (Token NestedComment (StringAttributes sval _)) = sval

attributes2string NoAttributes = ""
attributes2string (CharAttributes cval _) = showCh cval 
attributes2string (IntAttributes ival _) = show ival
attributes2string (FloatAttributes fval _) = show fval
attributes2string (IntegerAttributes intval _) = show intval
attributes2string (StringAttributes sval _) = showSt sval 
attributes2string (IdentAttributes mIdent ident) =concat (intersperse "." (mIdent ++ [ident])) 

basename = reverse .  takeWhile (/='/')    . reverse

-- showCh c = toString $ toGoodChar c
--toString c = "'" ++ c ++ "'"

showCh c    
   | c == '\\' = "'\\\\'"
   | elem c ('\127' : ['\001' .. '\031']) = show c
   | otherwise = toString c
  where
    toString c = "'" ++ c : "'"

showSt = addQuotes . concatMap toGoodChar 
   where
      addQuotes x = "\"" ++ x ++ "\""

toGoodChar c     
   | c == '\\' = "\\\\"
   | elem c ('\127' : ['\001' .. '\031']) = justShow c
   | c == '"' = "\\\""
   | otherwise = c : "" 
 where
     justShow = reverse . tail . reverse . tail . show  

     
--  DEBUGGING

tokenNcodes2codesLOG :: Int -> Int -> [(Position,Token)] -> [Code] -> IO [Code]
tokenNcodes2codesLOG _ _ [] _ = return []          
tokenNcodes2codesLOG currLine currCol toks@((Position _ line col,token):ts) codes 
    | currLine < line =
           appendFile "out/log.txt" ("Zeile: " ++ show currLine ++ "/" ++ show line ++ " Spalte: " ++ show currCol ++ "/" ++ show col  ++ " NewLines: " ++ show (line - currLine) ++ "\n") >>             
           tokenNcodes2codesLOG line 1 toks codes >>= \ temp ->
           return ((replicate (line - currLine) NewLine) ++ temp)
    | currCol < col =  
           appendFile "out/log.txt" ("Zeile: " ++ show currLine ++ "/" ++ show line ++ " Spalte: " ++ show currCol ++ "/" ++ show col  ++ " Space " ++ show (col - currCol)++ "\n") >>
           tokenNcodes2codesLOG currLine col toks codes >>= \ temp ->
           return (Space (col - currCol) : temp)           
    | isTokenIdentifier token && null codes =
           appendFile "out/log.txt" ("Zeile: " ++ show currLine ++ "/" ++ show line ++ " Spalte: " ++ show currCol ++ "/" ++ show col  ++ " error: empty Code-List, Token: " ++ show token ++ "\n") >>
           error ("empty Code-List, Token: " ++ show token)
    | not (isTokenIdentifier token) =
           appendFile "out/log.txt" ("Zeile: " ++ show currLine ++ "/" ++ show line ++ " Spalte: " ++ show currCol ++ "/" ++ show col  ++ " Token ist kein Identifier: " ++ tokenStr ++ "\n") >>
           tokenNcodes2codesLOG newLine newCol ts codes >>= \ temp ->
           return (token2code token : temp)                   
    | tokenStr == code2string (head codes) =
           appendFile "out/log.txt" ("Zeile: " ++ show currLine ++ "/" ++ show line ++ " Spalte: " ++ show currCol ++ "/" ++ show col  ++ " Code wird genommen: " ++ show (head codes) ++ "\n") >>
           tokenNcodes2codesLOG newLine newCol ts (tail codes)  >>= \ temp ->
           return (head codes : temp)                 
    | otherwise = 
           appendFile "out/log.txt" ("Zeile: " ++ show currLine ++ "/" ++ show line ++ " Spalte: " ++ show currCol ++ "/" ++ show col  ++ " Token: "++ tokenStr ++",Code fällt weg: " ++ show (head codes) ++ "\n") >>
           tokenNcodes2codesLOG currLine currCol toks (tail codes)
  where
      tokenStr = token2string token            
      newLine   = (currLine + length (lines tokenStr)) - 1 
      newCol  = currCol + length tokenStr   

     
  
--writeFile ("out/" ++ basename s) cont            
     
test2 s =
     readFile s >>= \ cont ->
     let (Result _ modul@(Module m e list)) = (parse s cont)
         (Result _ ls) = (Frontend.lex s cont) in
     writeFile ("out/" ++ basename s ++ ".parse.txt") 
               (show m ++
               " " ++
               show e ++
               "\n" ++
               unlines (map show list)) >>
     writeFile ("out/" ++ basename s ++ ".lex.txt") (unlines $ map show ls) >>
     writeFile ("out/" ++ basename s ++ ".ids.txt") (unlines $ map show (concatMap decl2codes list)) >>  
     writeFile "out/log.txt" "" >>
     writeFile ("out/" ++ basename s) cont >>    
     tokenNcodes2codesLOG 0 0 ls (catIdentifiers modul) >>= writeFile ("out/" ++ basename s ++ ".codes.txt") . unlines . map show

     
--writeFile ("out/" ++ basename s ++ ".codes.txt") (unlines $ map show (tokenNcodes2codes 1 1 ls (concatMap decl2codes list)))      