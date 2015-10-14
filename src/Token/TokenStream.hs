{- |
    Module      :  $Header$
    Description :  Generating List of Tokens and Positions

    This module defines a function for writing the list of tokens
    and positions of a Curry source module into a separate file.
-}

module TokenStream (source2token) where

import Curry.Base.Message    (showError)
import Curry.Base.Ident      (ModuleIdent (..), QualIdent (..), unqualify)
import Curry.Base.Monad      (CYIO, liftCYM, failMessages, runCYM)
import Curry.Base.Position
import Curry.Base.Pretty     (text)
import Curry.Files.PathUtils (readModule)
import Curry.Syntax          (Module (..), lexSource)

import Base.Messages         (warn, message)
import CompilerOpts          (Options (..), WarnOpts (..))
import CurryBuilder          (findCurry)

--inFile :: String
--inFile = "testAllTokens.curry"

--outFile :: String
--outFile = inFile ++ ".token"

-- |Write list of Tokens and Positions into a file
source2token :: Options -> String -> CYIO()
source2token opts s = do
  srcFile    <- findCurry opts s
  (mid, tok) <- formatToken opts srcFile
  outFile    <- tokenFile mid
  liftIO $ writeFile outFile tok

-- |Create TokenStream
formatToken :: Options -> String -> CYIO (ModuleIdent, String)
formatToken opts f = do
  mbModule <- liftIO $ readModule f
  case mbModule of
    Nothing  -> failMessages [message $ text $ "Missing file: " ++ f]
    Just src -> do
    case runCYM (lexSource f src) of
      Left errs -> putStrLn "ERROR" >> mapM_ (putStrLn . showError) errs
      Right toks -> return ({-moduleIdent m - woher?-}, show $ map (\(p, t) -> (p, showToken t)) toks)

-- |Generate filename for output from ModuleIdent
tokenFile :: ModuleIdent -> String
tokenFile m = show m ++ "_curry.token"

-- |Show tokens and their value if needed
showToken :: Token -> String
showToken t =
  case t of 
-- literals
    Token CharTok (CharAttributes cval original) -> "CharTok " ++ show cval
    Token IntTok  (IntAttributes  ival original) -> "IntTok " ++ show ival
    Token FloatTok (FloatAttributes fval original) -> "FloatTok " ++ show fval
    Token StringTok (StringAttributes sval original) -> "StringTok " ++ show sval

-- identifiers
    Token Id (IdentAttributes modulVal sval) -> "Id " ++ show sval
    Token QId (IdentAttributes modulVal sval) -> "QId " ++ show sval
    Token Sym (IdentAttributes modulVal sval) -> "Sym " ++ show sval
    Token QSym (IdentAttributes modulVal sval) -> "QSym " ++ show sval

-- punctuation symbols
    Token LeftParen NoAttributes -> "LeftParen"
    Token RightParen NoAttributes -> "RightParen"
    Token Semicolon NoAttributes -> "Semicolon"
    Token LeftBrace NoAttributes -> "LeftBrace"
    Token RightBrace NoAttributes -> "RightBrace"
    Token Comma NoAttributes -> "Comma"
    Token Underscore NoAttributes -> "Underscore"
    Token Backquote NoAttributes -> "Backquote"

-- layout
    Token LeftBraceSemicolon NoAttributes -> "LeftBracketSemicolon"
    Token VSemicolon NoAttributes -> "VSemicolon"
    Token VRightBrace NoAttributes -> "VRightBrace"

-- reserved keywords
    Token KW_case (IdentAttributes modulVal sval) -> "KW_case"
    Token KW_data (IdentAttributes modulVal sval) -> "KW_data"
    Token KW_do (IdentAttributes modulVal sval) -> "KW_do"
    Token KW_else (IdentAttributes modulVal sval) -> "KW_else"
    Token KW_external (IdentAttributes modulVal sval) -> "KW_external"
    Token KW_fcase (IdentAttributes modulVal sval) -> "KW_fcase"
    Token KW_foreign (IdentAttributes modulVal sval) -> "KW_foreign"
    Token KW_free (IdentAttributes modulVal sval) -> "KW_free"
    Token KW_if (IdentAttributes modulVal sval) -> "KW_if"
    Token KW_import (IdentAttributes modulVal sval) -> "KW_import"
    Token KW_in (IdentAttributes modulVal sval) -> "KW_in"
    Token KW_infix (IdentAttributes modulVal sval) -> "KW_infix"
    Token KW_infixl (IdentAttributes modulVal sval) -> "KW_infixl"
    Token KW_infixr (IdentAttributes modulVal sval) -> "KW_infixr"
    Token KW_let (IdentAttributes modulVal sval) -> "KW_let"
    Token KW_module (IdentAttributes modulVal sval) -> "KW_module"
    Token KW_newtype (IdentAttributes modulVal sval) -> "KW_newtype"
    Token KW_of (IdentAttributes modulVal sval) -> "KW_of"
    Token KW_then (IdentAttributes modulVal sval) -> "KW_then"
    Token KW_type (IdentAttributes modulVal sval) -> "KW_type"
    Token KW_where (IdentAttributes modulVal sval) -> "KW_where"

-- reserved operators
    Token At (IdentAttributes modulVal sval) -> "At"
    Token Colon (IdentAttributes modulVal sval) -> "Colon"
    Token DotDot (IdentAttributes modulVal sval) -> "DotDot"
    Token DoubleColon (IdentAttributes modulVal sval) -> "DoubleColon" 
    Token Equals (IdentAttributes modulVal sval) -> "Equals"
    Token Backslash (IdentAttributes modulVal sval) -> "Backslash"
    Token Bar (IdentAttributes modulVal sval) -> "Bar"
    Token LeftArrow (IdentAttributes modulVal sval) -> "LeftArrow"
    Token RightArrow (IdentAttributes modulVal sval) -> "RightArrow"
    Token Tilde (IdentAttributes modulVal sval) -> "Tilde"
    Token Bind (IdentAttributes modulVal sval) -> "Bind"
    Token Select (IdentAttributes modulVal sval) -> "Select"

-- special identifiers
    Token Id_as (IdentAttributes modulVal sval) -> "Id_as"
    Token Id_ccall (IdentAttributes modulVal sval) -> "Id_ccall"
    Token Id_forall (IdentAttributes modulVal sval) -> "Id_forall"
    Token Id_hiding (IdentAttributes modulVal sval) -> "Id_hiding"
    Token Id_interface (IdentAttributes modulVal sval) -> "Id_interface" 
    Token Id_primitive (IdentAttributes modulVal sval) -> "Id_primitive"
    Token Id_qualified (IdentAttributes modulVal sval) -> "Id_qualified"

-- special operators
    Token SymDot (IdentAttributes modulVal sval) -> "SymDot"
    Token SymMinus (IdentAttributes modulVal sval) -> "SymMinus"
    Token SymMinusDot (IdentAttributes modulVal sval) -> "SymMinusDot"

-- pragmas
    Token PragmaLanguage NoAttributes -> "PragmaLanguage"
    Token PragmaOptions (OptionsAttributes toolVal toolArgs) -> "PragmaOptions " ++ show toolArgs
    Token PragmaHiding NoAttributes -> "PragmaHiding" 
    Token PragmaEnd NoAttributes -> "PragmaEnd" 

-- comments
    Token LineComment (StringAttributes sval original) -> "LineComment " ++ show sval
    Token NestedComment (StringAttributes sval original) -> "NestedComment " ++ show sval

-- end-of-file token
    Token EOF NoAttributes -> "EOF"

-- else
    _ -> show t
