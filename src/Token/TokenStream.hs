{- |
    Module      :  $Header$
    Description :  Generating List of Tokens and Positions

    This module defines a function for writing the list of tokens
    and positions of a Curry source module into a separate file.
-}

module Token.TokenStream (source2token) where

import Control.Monad.Writer  (liftIO)
import Data.List             (intercalate)
import System.FilePath       (replaceExtension)

import Curry.Base.Monad      (CYIO, liftCYM, failMessages, runCYMIgnWarn)
import Curry.Base.Position   (Position (..))
import Curry.Base.Pretty     (text)
import Curry.Files.Filenames (addCurrySubdirModule)
import Curry.Files.PathUtils (readModule)
import Curry.Syntax          -- import data constructors for all tokens

import Base.Messages         (abortWithMessages, message, Message)
import CompilerOpts          (Options (..))
import CurryBuilder          (findCurry)

-- |Write list of tokens and positions into a file
-- TODO: To get the name of the module its header is getting parsed.
--       This should be improved because there shouldn't be done any
--       parsing when extracting only the TokenStream.
source2token :: Options -> String -> CYIO()
source2token opts s = do
  srcFile              <- findCurry opts s
  parse                <- (liftCYM $ parseHeader srcFile s)
  (Module _ mid _ _ _) <- return $ patchModuleId srcFile parse
  eitherErrsToks       <- formatToken srcFile
  outFile              <- return $ replaceExtension (addCurrySubdirModule (optUseSubdir opts) mid srcFile) ".token"
  case eitherErrsToks of
    Left errs -> liftIO $ abortWithMessages errs
    Right toks -> do let content = showTokenStream toks -- $ map (\(p, t) -> (p, showToken t)) toks
                     liftIO $ writeFile outFile content

showTokenStream :: [(Position, Token)] -> String
showTokenStream [] = "[]"
showTokenStream ts = "[ " ++ intercalate "\n, " (map showPosToken ts) ++ "\n]\n"
  where showPosToken (p, t) = "(" ++ showPosition p ++
                              ", " ++ showToken t ++ ")"

-- show position as "(line, column)"
showPosition :: Position -> String
showPosition p = "(" ++ (show $ line p) ++ ", " ++ (show $ column p) ++ ")"

-- |Create list of tokens and their positions from curry source file
formatToken :: String -> CYIO (Either [Message] [(Position, Token)])
formatToken f = do
  mbModule <- liftIO $ readModule f
  case mbModule of
    Nothing  -> failMessages [message $ text $ "Missing file: " ++ f]
    Just src -> return $ runCYMIgnWarn (lexSource f src)

-- |Show tokens and their value if needed
showToken :: Token -> String
showToken t =
  case t of
-- literals
    Token CharTok (CharAttributes cvalue _)     -> "CharTok "   ++ show cvalue
    Token IntTok  (IntAttributes  ivalue _)     -> "IntTok "    ++ show ivalue
    Token FloatTok (FloatAttributes fvalue _)   -> "FloatTok "  ++ show fvalue
    Token StringTok (StringAttributes svalue _) -> "StringTok " ++ show svalue

-- identifiers
    Token Id (IdentAttributes _ svalue)   -> "Id "   ++ show svalue
    Token QId (IdentAttributes _ svalue)  -> "QId "  ++ show svalue
    Token Sym (IdentAttributes _ svalue)  -> "Sym "  ++ show svalue
    Token QSym (IdentAttributes _ svalue) -> "QSym " ++ show svalue

-- punctuation symbols
    Token LeftParen NoAttributes    -> "LeftParen"
    Token RightParen NoAttributes   -> "RightParen"
    Token Semicolon NoAttributes    -> "Semicolon"
    Token LeftBrace NoAttributes    -> "LeftBrace"
    Token RightBrace NoAttributes   -> "RightBrace"
    Token LeftBracket NoAttributes  -> "LeftBracket"
    Token RightBracket NoAttributes -> "RightBracket"
    Token Comma NoAttributes        -> "Comma"
    Token Underscore NoAttributes   -> "Underscore"
    Token Backquote NoAttributes    -> "Backquote"

-- layout
    Token VSemicolon NoAttributes         -> "VSemicolon"
    Token VRightBrace NoAttributes        -> "VRightBrace"

-- reserved keywords
    Token KW_case (IdentAttributes _ _)     -> "KW_case"
    Token KW_data (IdentAttributes _ _)     -> "KW_data"
    Token KW_do (IdentAttributes _ _)       -> "KW_do"
    Token KW_else (IdentAttributes _ _)     -> "KW_else"
    Token KW_external (IdentAttributes _ _) -> "KW_external"
    Token KW_fcase (IdentAttributes _ _)    -> "KW_fcase"
    Token KW_foreign (IdentAttributes _ _)  -> "KW_foreign"
    Token KW_free (IdentAttributes _ _)     -> "KW_free"
    Token KW_if (IdentAttributes _ _)       -> "KW_if"
    Token KW_import (IdentAttributes _ _)   -> "KW_import"
    Token KW_in (IdentAttributes _ _)       -> "KW_in"
    Token KW_infix (IdentAttributes _ _)    -> "KW_infix"
    Token KW_infixl (IdentAttributes _ _)   -> "KW_infixl"
    Token KW_infixr (IdentAttributes _ _)   -> "KW_infixr"
    Token KW_let (IdentAttributes _ _)      -> "KW_let"
    Token KW_module (IdentAttributes _ _)   -> "KW_module"
    Token KW_newtype (IdentAttributes _ _)  -> "KW_newtype"
    Token KW_of (IdentAttributes _ _)       -> "KW_of"
    Token KW_then (IdentAttributes _ _)     -> "KW_then"
    Token KW_type (IdentAttributes _ _)     -> "KW_type"
    Token KW_where (IdentAttributes _ _)    -> "KW_where"

-- reserved operators
    Token At (IdentAttributes _ _)          -> "At"
    Token Colon (IdentAttributes _ _)       -> "Colon"
    Token DotDot (IdentAttributes _ _)      -> "DotDot"
    Token DoubleColon (IdentAttributes _ _) -> "DoubleColon"
    Token Equals (IdentAttributes _ _)      -> "Equals"
    Token Backslash (IdentAttributes _ _)   -> "Backslash"
    Token Bar (IdentAttributes _ _)         -> "Bar"
    Token LeftArrow (IdentAttributes _ _)   -> "LeftArrow"
    Token RightArrow (IdentAttributes _ _)  -> "RightArrow"
    Token Tilde (IdentAttributes _ _)       -> "Tilde"
    Token Bind (IdentAttributes _ _)        -> "Bind"
    Token Select (IdentAttributes _ _)      -> "Select"

-- special identifiers
    Token Id_as (IdentAttributes _ _)        -> "Id_as"
    Token Id_ccall (IdentAttributes _ _)     -> "Id_ccall"
    Token Id_forall (IdentAttributes _ _)    -> "Id_forall"
    Token Id_hiding (IdentAttributes _ _)    -> "Id_hiding"
    Token Id_interface (IdentAttributes _ _) -> "Id_interface"
    Token Id_primitive (IdentAttributes _ _) -> "Id_primitive"
    Token Id_qualified (IdentAttributes _ _) -> "Id_qualified"

-- special operators
    Token SymDot (IdentAttributes _ _)      -> "SymDot"
    Token SymMinus (IdentAttributes _ _)    -> "SymMinus"
    Token SymMinusDot (IdentAttributes _ _) -> "SymMinusDot"

-- pragmas
    Token PragmaLanguage NoAttributes                   -> "PragmaLanguage"
    Token PragmaOptions (OptionsAttributes _ toolArgs_) -> "PragmaOptions " ++ show toolArgs_
    Token PragmaHiding NoAttributes                     -> "PragmaHiding"
    Token PragmaEnd NoAttributes                        -> "PragmaEnd"

-- comments
    Token LineComment (StringAttributes svalue _)   -> "LineComment "   ++ show svalue
    Token NestedComment (StringAttributes svalue _) -> "NestedComment " ++ show svalue

-- end-of-file token
    Token EOF NoAttributes -> "EOF"

-- else
    _ -> show t
