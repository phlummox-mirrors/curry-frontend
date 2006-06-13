module CurryHtml(program2html,htmlMain,source2html) where

import SyntaxColoring
import Ident
import Maybe
import Char
import System.Environment
import Variables

htmlMain :: IO()
htmlMain = do
    args <- getArgs    
    if length args < 4
      then putStrLn ("usage: source2html <directoryOfFile> <modulname>"++
                    " <outputDirectory> ") >>
           putStrLn ("e.g. source2html /home/user/ Test"++
                     " /home/user/ ")
      else do
        let (_:dirOfFile:modulname:outputDir:_) = args
        source2html dirOfFile modulname outputDir 
       
--- translate source file into HTML file with syntaxcoloring
--- @param Directory of Module
--- @param Modulname
--- @param Directory of Outputfile
source2html :: String -> String -> String -> IO ()
source2html dirOfFile modulname outputDir = do
        program <- filename2program (dirOfFile ++ modulname ++ ".curry")
        writeFile (outputDir ++ modulname ++ "_curry.html")
                  (program2html modulname program)
   
       
--- generates htmlcode with syntax highlighting            
--- @param modulname
--- @param a program
--- @return HTMLcode
program2html :: String ->Program -> String
program2html modulname codes =
    "<HTML>\n<HEAD>\n<title>Module "++ 
    modulname++
    "</title>\n" ++
    "<link rel=\"stylesheet\" type=\"text/css\" href=\"currydoc.css\">"++
    "</link>\n</HEAD>\n<BODY style=\"font-family:'Courier New', Arial;\">\n<PRE>\n" ++
    concat (map (code2html True . (\(_,_,c) -> c)) codes) ++
    "<PRE>\n</BODY>\n</HTML>"            
            
            
--- which code has which color 
--- @param code
--- @return color of the code  
code2class :: Code -> String                          
code2class (Keyword _) = "keyword"
code2class (Space _)= ""
code2class NewLine = ""
code2class (ConstructorName _ _) = "constructorName"
code2class (Function _ _) = "function"
code2class (ModuleName _) = "moduleName"
code2class (Commentary _) = "commentary"
code2class (NumberCode _) = "numberCode"
code2class (StringCode _) = "stringCode"
code2class (CharCode _) = "charCode"
code2class (Symbol _) = "symbol"
code2class (Identifier _ _) = "identifier"
code2class (TypeConstructor _ _) = "typeConstructor"
code2class (CodeError _ _) = "codeError"
code2class (CodeWarning _ _) = "codeWarning"
code2class (NotParsed _) = "notParsed"


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
                      (code2string c)                                    
                                        
                                        
spanTag :: String -> String -> String
spanTag cl str
   |null cl = str
   | otherwise = "<SPAN class=\""++ cl ++ "\">" ++ str ++ "</SPAN>"

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


fileName s = reverse (takeWhile (/='/') (reverse s))



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
  
