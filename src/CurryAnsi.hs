module CurryAnsi(program2ansi) where

import SyntaxColoring
import AnsiCodes


code2color :: Code -> String -> String                          
code2color (Keyword _) = bold . blue
code2color (Space _)= id
code2color NewLine = id
code2color (ConstructorName _ _) = magenta
code2color (Function _ _) = yellow
code2color (ModuleName _) = cyan
code2color (Commentary _) = green
code2color (NumberCode _) = white
code2color (StringCode _) = white
code2color (CharCode _) = white
code2color (Symbol _) = id
code2color (Identifier _ _) = blue
code2color (TypeConstructor _ _) = bold . magenta
code2color (CodeError _ _) = bgRed
code2color (CodeWarning _ _) = red
code2color (NotParsed _) = red

program2ansi :: Program -> String
program2ansi codes =  concatMap (code2ansi True . (\(_,_,c) -> c)) codes    

code2ansi :: Bool -> Code -> String    
code2ansi _ code@(CodeError _ c) =
      (code2color code) (code2ansi False c)
code2ansi ownColor code@(CodeWarning _ c) =
     (if ownColor then (code2color code) else id) (code2ansi False c)              
code2ansi ownColor c =
     (if ownColor then (code2color c) else id) (code2string c) 
     