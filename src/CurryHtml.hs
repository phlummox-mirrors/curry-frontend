module CurryHtml where

import SyntaxColoring
import Ident

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

            
code2color (Keyword _) = Blue
code2color (Space _)= White
code2color NewLine = White
code2color (ConstructorName _ _) = Fuchsia
code2color (Function _ _) = Purple
code2color (ModuleName _) = Maroon
code2color (Commentary _) = Green
code2color (NumberCode _) = Black
code2color (StringCode _) = Blue
code2color (CharCode _) = Blue
code2color (Symbol _) = Silver
code2color (Identifier _ _) = Black
code2color (TypeConstructor _) = Blue


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

program2html (Program codes unparsed) =
    "<HTML><HEAD></HEAD><BODY style=\"font-family:'Courier New', Arial;\">" ++
    concat (map code2html codes ++ [unparsed2html unparsed]) ++
    "</BODY></HTML>"
 

code2html c  
      | isCall c = maybe tag (addHtmlLink tag) (getQualIdent c) 
      | isDecl c = maybe tag (addHtmlAnker tag) (getQualIdent c)
      | otherwise = tag
    where tag = spanTag (color2html (code2color c)) 
                      (replace ' ' 
                               "&nbsp;" 
                               (replace '\n' 
                                        "<br>\n" 
                                        (code2string c)))                                    
                                        
                                        
spanTag :: String -> String -> String
spanTag color str = "<SPAN style=\"color:"++ color ++"\">" ++ str ++ "</SPAN>"



unparsed2html str = spanTag "red" $ replace ' ' "&nbsp;" $ replace '\n' "<br>" str

replace :: Char -> String -> String -> String
replace old new = foldr (\ x -> if x == old then (new ++) else ([x]++)) ""

addHtmlAnker :: String -> QualIdent -> String
addHtmlAnker html qualIdent = "<a name=\""++ show qualIdent ++"\"></a>" ++ html

addHtmlLink :: String -> QualIdent -> String
addHtmlLink html qualIdent =
   "<a href=\"#"++ show qualIdent ++"\">"++ html ++"</a>"


isCall :: Code -> Bool
isCall code = if isDecl code
                then False
                else isCall_helper code
  where
     isCall_helper (ConstructorName _ _) = True
     isCall_helper (Function _ _) = True
     isCall_helper (Identifier _ _) = True
     isCall_helper _ = False

isDecl :: Code -> Bool
isDecl (ConstructorName ConstrDecla _) = True
isDecl (Function FunDecl _) = True
isDecl (Identifier IdDecl _) = True
isDecl _ = False 

addModuleIdent :: ModuleIdent -> Code -> Code
addModuleIdent moduleIdent (Function FunDecl qualIdent) 
    | uniqueId (unqualify qualIdent) == 0 =
        (Function FunDecl (qualQualify moduleIdent qualIdent))
    | otherwise = (Function FunDecl qualIdent)
addModuleIdent _ c = c
