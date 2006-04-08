module CurryHtml(program2html) where

import SyntaxColoring
import Ident
import Maybe
import Char

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
            |RGB String


code2color :: Code -> Color                          
code2color (Keyword _) = Blue
code2color (Space _)= White
code2color NewLine = White
code2color (ConstructorName _ _) = Fuchsia
code2color (Function _ _) = Purple
code2color (ModuleName _) = Maroon
code2color (Commentary _) = Green
code2color (NumberCode _) = RGB "#008080"
code2color (StringCode _) = RGB "#800000"
code2color (CharCode _) = RGB "#FFFF00"
code2color (Symbol _) = Silver
code2color (Identifier _ _) = Black
code2color (TypeConstructor _ _) = RGB "#ff7f50"
code2color (CodeError _ _) = RGB "#a52a2a"
code2color (CodeWarning _ _) = Red
code2color (NotParsed _) = Silver

color2html :: Color -> String
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
color2html (RGB str) = str

program2html :: Program -> String
program2html codes =
    "<HTML><HEAD></HEAD><BODY style=\"font-family:'Courier New', Arial;\">" ++
    concat (map (code2html True . (\(_,_,c) -> c)) codes) ++
    "</BODY></HTML>"
 

code2html :: Bool -> Code -> String    
code2html _ code@(CodeError _ c) =
      (spanTag (color2html (code2color code)) 
              (code2html False c))
code2html ownColor code@(CodeWarning _ c) =
     (if ownColor then spanTag (color2html (code2color code)) else id)
              (code2html False c)              
code2html ownColor c
      | isCall c && ownColor = maybe tag (addHtmlLink tag) (getQualIdent c) 
      | isDecl c && ownColor= maybe tag (addHtmlAnker tag) (getQualIdent c)
      | otherwise = tag
    where tag = (if ownColor then spanTag (color2html (code2color c)) else id)
                      (replace ' ' 
                               "&nbsp;" 
                               (replace '\n' 
                                        "<br>\n" 
                                        (code2string c)))                                    
                                        
                                        
spanTag :: String -> String -> String
spanTag color str = "<SPAN style=\"color:"++ color ++"\">" ++ str ++ "</SPAN>"

replace :: Char -> String -> String -> String
replace old new = foldr (\ x -> if x == old then (new ++) else ([x]++)) ""

addHtmlAnker :: String -> QualIdent -> String
addHtmlAnker html qualIdent = "<a name=\""++ string2urlencoded (show (unqualify qualIdent)) ++"\"></a>" ++ html

addHtmlLink :: String -> QualIdent -> String
addHtmlLink html qualIdent =
   let (maybeModuleIdent,ident) = splitQualIdent qualIdent in   
   "<a href=\"" ++ 
   (maybe "" (\x -> show x ++ ".curry.html") maybeModuleIdent) ++ 
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



genHtmlFile :: String -> IO ()
genHtmlFile moduleName = 
  filename2program ["/home/pakcs/pakcs/lib"] 
    (moduleName++".curry") >>= \ x -> seq x $
  writeFile (fileName moduleName++".html") (program2html x) 

fileName s = reverse (takeWhile (/='/') (reverse s))



--- Translates arbitrary strings into equivalent urlencoded string.
string2urlencoded :: String -> String
string2urlencoded [] = []
string2urlencoded (c:cs)
  | isAlphaNum c = c : string2urlencoded cs
  | c == ' '     = '+' : string2urlencoded cs
  | otherwise = show (ord c) ++ (if null cs then "" else ".") ++ string2urlencoded cs
  
