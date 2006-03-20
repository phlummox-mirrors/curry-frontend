module CurryHtml where

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
code2color (NotParsed _) = Red

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
program2html (Program moduleIdent codes) =
    "<HTML><HEAD></HEAD><BODY style=\"font-family:'Courier New', Arial;\">" ++
    concat (map (code2html moduleIdent True . addModuleIdent moduleIdent) codes) ++
    "</BODY></HTML>"
 

code2html :: ModuleIdent -> Bool -> Code -> String    
code2html moduleIdent _ code@(CodeError _ codes) =
      (spanTag (color2html (code2color code)) 
              (concatMap (code2html moduleIdent False) codes))
code2html moduleIdent ownColor code@(CodeWarning _ codes) =
     (if ownColor then spanTag (color2html (code2color code)) else id)
              (concatMap (code2html moduleIdent False) codes)              
code2html moduleIdent ownColor c
      | isCall c && ownColor = maybe tag (addHtmlLink moduleIdent tag) (getQualIdent c) 
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

addHtmlLink :: ModuleIdent -> String -> QualIdent -> String
addHtmlLink moduleIdent html qualIdent =
   let (maybeModuleIdent,ident) = splitQualIdent qualIdent in   
   "<a href=\"" ++ prefix maybeModuleIdent ++ "#"++ string2urlencoded (show ident) ++"\">"++ html ++"</a>"
 where
    prefix maybeModuleIdent = 
          if maybe True (== moduleIdent) maybeModuleIdent
                then ""
                else show (fromJust maybeModuleIdent) ++ ".curry.html"   


isCall :: Code -> Bool
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
  filename2Qualifiedprogram ["/home/pakcs/pakcs/lib"] 
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
  
--  | otherwise = let oc = ord c
--    in '%' : int2hex(oc `div` 16) : int2hex(oc `mod` 16) : string2urlencoded cs
-- where
--   int2hex i = if i<10 then chr (ord '0' + i)
--                       else chr (ord 'A' + i - 10)