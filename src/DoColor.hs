import SyntaxColoring
import System.Environment
import Frontend
import CurrySyntax
import CurryHtml

main = getArgs >>= test 

test (s:paths) = filename2Qualifiedprogram paths s >>= \prog ->
         writeFile (basename s ++ ".html") (program2html prog) 
         

