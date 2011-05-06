{- |A simple interface for reading and manipulating Curry source code.

    (c) 2009, Holger Siegel
        2011, Björn Peemöller
-}
module Curry.Syntax
  ( module Curry.Syntax.Type
  , module Curry.Syntax.Utils
  , lexFile
  , parseHeader
  , parseModule
  , ppModule, ppIDecl
  , showModule
  ) where

import Curry.Base.Position (Position, first)
import Curry.Base.MessageMonad (MsgMonad)
import Curry.Files.Unlit (unlit)
import qualified Curry.Syntax.Lexer as Lexer (Token, lexFile)
import qualified Curry.Syntax.Parser as Parser (parseHeader, parseSource)
import Curry.Syntax.Pretty (ppModule, ppIDecl)
import Curry.Syntax.ShowModule (showModule)
import Curry.Syntax.Type
import Curry.Syntax.Utils

{- |Return the result of a lexical analysis of the source program 'src'.
    The result is a list of tuples consisting of a 'Position' and a 'Token'
-}
lexFile :: FilePath -> String -> MsgMonad [(Position, Lexer.Token)]
lexFile fn src = unlit fn src >>= \s -> Lexer.lexFile (first fn) s False []

-- | Parse a curry header
parseHeader :: FilePath -> String -> MsgMonad Module
parseHeader fn src = unlit fn src >>= Parser.parseHeader fn

-- | Parse a curry module
parseModule :: Bool -> FilePath -> String -> MsgMonad Module
parseModule likeFlat fn src = unlit fn src >>= Parser.parseSource likeFlat fn
