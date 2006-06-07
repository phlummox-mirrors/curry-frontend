module GenSourceFile where

import SyntaxColoring
import CurryHtml
import System.Environment

main :: IO()
main = do
    args <- getArgs
    if length args < 3
      then putStrLn ("usage: GenSourceFile <directoryOfFile> <modulname>"++
                    " <outputDirectory> [<importDirectory>"++
                    " <importDirectory> ...]") >>
           putStrLn ("e.g. GenSourceFile /home/user/ Test"++
                     " /home/user/ /home/user/lib/")
      else do
        let (dirOfFile:modulname:outputDir:importDirs) = args
        program <- filename2program (dirOfFile:importDirs) 
                                    (dirOfFile ++ modulname ++ ".curry")
        writeFile (outputDir ++ modulname ++ "_curry.html")
                  (program2html program)