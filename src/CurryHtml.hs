module CurryHtml(program2html,source2html) where

import SyntaxColoring
import Ident
import Maybe
import Char
import System.Environment
import CurryDeps(getCurryPath)
import PathUtils (writeModule)
       
--- translate source file into HTML file with syntaxcoloring
--- @param outputfilename
--- @param sourcefilename
source2html :: [String] -> String -> String -> IO ()
source2html imports outputfilename sourcefilename = do
        let sourceprogname = removeExtension sourcefilename
            output = if null outputfilename 
                     then sourceprogname ++ "_curry.html"
                     else outputfilename 
            modulname = fileName sourceprogname
        fullfname <- getCurryPath imports [] sourcefilename
        program <- filename2program imports (maybe sourcefilename id fullfname)
        writeModule output 
                  (program2html modulname program)
   
       
--- generates htmlcode with syntax highlighting            
--- @param modulname
--- @param a program
--- @return HTMLcode
program2html :: String ->Program -> String
program2html modulname codes =
    "<html>\n<head>\n<title>Module "++ 
    modulname++
    "</title>\n" ++
    "<link rel=\"stylesheet\" type=\"text/css\" href=\"currydoc.css\">"++
    "</link>\n</head>\n<body style=\"font-family:'Courier New', Arial;\">\n<pre>\n" ++
    concat (map (code2html True . (\(_,_,c) -> c)) codes) ++
    "<pre>\n</body>\n</html>"            
            
            
--- which code has which color 
--- @param code
--- @return color of the code  
code2class :: Code -> String                          
code2class (Keyword _) = "keyword"
code2class (Space _)= ""
code2class NewLine = ""
code2class (ConstructorName ConstrPattern _) = "constructorname_constrpattern"
code2class (ConstructorName ConstrCall _) = "constructorname_constrcall"
code2class (ConstructorName ConstrDecla _) = "constructorname_constrdecla"
code2class (ConstructorName OtherConstrKind _) = "constructorname_otherconstrkind"
code2class (Function InfixFunction _) = "function_infixfunction"
code2class (Function TypSig _) = "function_typsig"
code2class (Function FunDecl _) = "function_fundecl"
code2class (Function FunctionCall _) = "function_functioncall"
code2class (Function OtherFunctionKind _) = "function_otherfunctionkind"
code2class (ModuleName _) = "modulename"
code2class (Commentary _) = "commentary"
code2class (NumberCode _) = "numbercode"
code2class (StringCode _) = "stringcode"
code2class (CharCode _) = "charcode"
code2class (Symbol _) = "symbol"
code2class (Identifier IdDecl _) = "identifier_iddecl"
code2class (Identifier IdOccur _) = "identifier_idoccur"
code2class (Identifier UnknownId _) = "identifier_unknownid"
code2class (TypeConstructor TypeDecla _) = "typeconstructor_typedecla"
code2class (TypeConstructor TypeUse _) = "typeconstructor_typeuse"
code2class (TypeConstructor TypeExport _) = "typeconstructor_typeexport"
code2class (CodeError _ _) = "codeerror"
code2class (CodeWarning _ _) = "codewarning"
code2class (NotParsed _) = "notparsed"


code2html :: Bool -> Code -> String    
code2html _ code@(CodeError _ c) =
      (spanTag (code2class code) 
              (code2html False c))
code2html ownClass code@(CodeWarning _ c) =
     (if ownClass then spanTag (code2class code) else id)
              (code2html False c)       
code2html ownClass code@(Commentary _) =
    (if ownClass then spanTag (code2class code) else id)
      (replace '<' "<span>&lt</span>" (code2string code))                
code2html ownClass c
      | isCall c && ownClass = maybe tag (addHtmlLink tag) (getQualIdent c) 
      | isDecl c && ownClass= maybe tag (addHtmlAnchor tag) (getQualIdent c)
      | otherwise = tag
    where tag = (if ownClass then spanTag (code2class c) else id)
                      (htmlQuote (code2string c)) 
                                        
spanTag :: String -> String -> String
spanTag cl str
   |null cl = str
   | otherwise = "<span class=\""++ cl ++ "\">" ++ str ++ "</span>"

replace :: Char -> String -> String -> String
replace old new = foldr (\ x -> if x == old then (new ++) else ([x]++)) ""

addHtmlAnchor :: String -> QualIdent -> String
addHtmlAnchor html qualIdent = "<a name=\""++ string2urlencoded (show (unqualify qualIdent)) ++"\"></a>" ++ html

addHtmlLink :: String -> QualIdent -> String
addHtmlLink html qualIdent =
   let (maybeModuleIdent,ident) = splitQualIdent qualIdent in   
   "<a href=\"" ++ 
   (maybe "" (\x -> show x ++ "_curry.html") maybeModuleIdent) ++ 
   "#"++ 
   string2urlencoded (show ident) ++
   "\">"++ 
   html ++
   "</a>"

isCall :: Code -> Bool
isCall (TypeConstructor TypeExport _) = True
isCall (TypeConstructor _ _) = False
isCall (Identifier _ _) = False
isCall code = not (isDecl code) &&
                maybe False (const True) (getQualIdent code)

     
isDecl :: Code -> Bool
isDecl (ConstructorName ConstrDecla _) = True
isDecl (Function FunDecl _) = True
isDecl (TypeConstructor TypeDecla _) = True
isDecl _ = False 


fileName = reverse . takeWhile (/='/') . reverse 

removeExtension = reverse . drop 1 . dropWhile (/='.') . reverse 


--- Translates arbitrary strings into equivalent urlencoded string.
string2urlencoded :: String -> String
string2urlencoded = id
{-
string2urlencoded [] = []
string2urlencoded (c:cs)
  | isAlphaNum c = c : string2urlencoded cs
  | c == ' '     = '+' : string2urlencoded cs
  | otherwise = show (ord c) ++ (if null cs then "" else ".") ++ string2urlencoded cs
-}

htmlQuote :: String -> String
htmlQuote [] = []
htmlQuote (c:cs) | c=='<' = "&lt;"   ++ htmlQuote cs
                 | c=='>' = "&gt;"   ++ htmlQuote cs
                 | c=='&' = "&amp;"  ++ htmlQuote cs
                 | c=='"' = "&quot;" ++ htmlQuote cs
                 | c=='\228' = "&auml;" ++ htmlQuote cs
                 | c=='\246' = "&ouml;" ++ htmlQuote cs
                 | c=='\252' = "&uuml;" ++ htmlQuote cs
                 | c=='\196' = "&Auml;" ++ htmlQuote cs
                 | c=='\214' = "&Ouml;" ++ htmlQuote cs
                 | c=='\220' = "&Uuml;" ++ htmlQuote cs
                 | c=='\223' = "&szlig;"++ htmlQuote cs
                 | otherwise = c : htmlQuote cs
  