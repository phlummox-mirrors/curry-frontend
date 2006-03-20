import SyntaxColoring
import System.Environment
import Frontend
import CurrySyntax
import CurryHtml
import CurryAnsi

main = getArgs >>= test

test (s:p:paths) = filename2Qualifiedprogram paths s >>= \prog ->
         writeFile (p ++ basename s ++ ".html") (program2html prog) 
         

test2 (s:paths) = filename2Qualifiedprogram paths s >>= \prog ->
         putStr (program2ansi prog) 