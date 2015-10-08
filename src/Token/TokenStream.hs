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


-- old code:
--source2tokenTest :: IO ()
--source2tokenTest = do
  --src <- readFile inFile
  --case runCYM (lexSource inFile src) of
    --Left  errs -> putStrLn "ERROR" >> mapM_ (putStrLn . showError) errs
    -- FIRST IMPLEMENTATION prints list with formated tokens, keeps pair-structure, maybe better for further processing
    --Right toks -> writeFile outFile $ show $ map (\(p, t) -> (p, showToken t)) toks 
    -- SECOND IMPLEMENTATION alternatively: prints single tokens with help of showPosToken; human-readable
    -- Right toks -> writeFile outFile $ foldr (++)  "" $ map (showPosToken) toks

-- SECOND; not needed for FIRST IMPLEMENTATION
-- showPosToken :: (Position, Token) -> String
-- showPosToken (p,t) = show p ++ "    " ++ showToken t

--inFile :: String
--inFile = "testAllTokens.curry"

--outFile :: String
--outFile = inFile ++ ".token"

-- |Get list of Tokens and Positions into a nice format
showToken :: Token -> String
showToken t =
  case t of 
-- literals
    Token CharTok (CharAttributes cval original) -> "CharTok " ++ show cval ++ "\n"
    Token IntTok  (IntAttributes  ival original) -> "IntTok " ++ show ival ++ "\n"
    Token FloatTok (FloatAttributes fval original) -> "FloatTok " ++ show fval ++ "\n"
    Token StringTok (StringAttributes sval original) -> "StringTok " ++ show sval ++ "\n"

-- identifiers
    Token Id (IdentAttributes modulVal sval) -> "Id " ++ show sval ++ "\n"
    Token QId (IdentAttributes modulVal sval) -> "QId " ++ show sval ++ "\n"
    Token Sym (IdentAttributes modulVal sval) -> "Sym " ++ show sval ++ "\n"
    Token QSym (IdentAttributes modulVal sval) -> "QSym " ++ show sval ++ "\n"

-- punctuation symbols
    Token LeftParen NoAttributes -> "LeftParen (\n"
    Token RightParen NoAttributes -> "RightParen )\n"
    Token Semicolon NoAttributes -> "Semicolon ;\n"
    Token LeftBrace NoAttributes -> "LeftBrace {\n"
    Token RightBrace NoAttributes -> "RightBrace }\n"
    Token Comma NoAttributes -> "Comma ,\n"
    Token Underscore NoAttributes -> "Underscore _\n"
    Token Backquote NoAttributes -> "Backquote `\n"

-- layout
    Token LeftBraceSemicolon NoAttributes -> "LeftBracketSemicolon \"{;\"\n"
    Token VSemicolon NoAttributes -> "VSemicolon \";\"\n"
    Token VRightBrace NoAttributes -> "VRightBrace \"}\"\n"

-- reserved keywords
    Token KW_case (IdentAttributes modulVal sval) -> "KW_case " ++ show sval ++ "\n"
    Token KW_data (IdentAttributes modulVal sval) -> "KW_data " ++ show sval ++ "\n"
    Token KW_do (IdentAttributes modulVal sval) -> "KW_do " ++ show sval ++ "\n"
    Token KW_else (IdentAttributes modulVal sval) -> "KW_else " ++ show sval ++ "\n"
    Token KW_external (IdentAttributes modulVal sval) -> "KW_external " ++ show sval ++ "\n"
    Token KW_fcase (IdentAttributes modulVal sval) -> "KW_fcase " ++ show sval ++ "\n"
    Token KW_foreign (IdentAttributes modulVal sval) -> "KW_foreign " ++ show sval ++ "\n"
    Token KW_free (IdentAttributes modulVal sval) -> "KW_free " ++ show sval ++ "\n"
    Token KW_if (IdentAttributes modulVal sval) -> "KW_if " ++ show sval ++ "\n"
    Token KW_import (IdentAttributes modulVal sval) -> "KW_import " ++ show sval ++ "\n"
    Token KW_in (IdentAttributes modulVal sval) -> "KW_in " ++ show sval ++ "\n"
    Token KW_infix (IdentAttributes modulVal sval) -> "KW_infix " ++ show sval ++ "\n"
    Token KW_infixl (IdentAttributes modulVal sval) -> "KW_infixl " ++ show sval ++ "\n"
    Token KW_infixr (IdentAttributes modulVal sval) -> "KW_infixr " ++ show sval ++ "\n"
    Token KW_let (IdentAttributes modulVal sval) -> "KW_let " ++ show sval ++ "\n"
    Token KW_module (IdentAttributes modulVal sval) -> "KW_module " ++ show sval ++ "\n"
    Token KW_newtype (IdentAttributes modulVal sval) -> "KW_newtype " ++ show sval ++ "\n"
    Token KW_of (IdentAttributes modulVal sval) -> "KW_of " ++ show sval ++ "\n"
    Token KW_then (IdentAttributes modulVal sval) -> "KW_then " ++ show sval ++ "\n"
    Token KW_type (IdentAttributes modulVal sval) -> "KW_type " ++ show sval ++ "\n"
    Token KW_where (IdentAttributes modulVal sval) -> "KW_where " ++ show sval ++ "\n"

-- reserved operators
    Token At (IdentAttributes modulVal sval) -> "At " ++ show sval ++ "\n"
    Token Colon (IdentAttributes modulVal sval) -> "Colon " ++ show sval ++ "\n"
    Token DotDot (IdentAttributes modulVal sval) -> "DotDot " ++ show sval ++ "\n"
    Token DoubleColon (IdentAttributes modulVal sval) -> "DoubleColon " ++ show sval ++ "\n"
    Token Equals (IdentAttributes modulVal sval) -> "Equals " ++ show sval ++ "\n"
    Token Backslash (IdentAttributes modulVal sval) -> "Backslash " ++ show sval ++ "\n"
    Token Bar (IdentAttributes modulVal sval) -> "Bar " ++ show sval ++ "\n"
    Token LeftArrow (IdentAttributes modulVal sval) -> "LeftArrow " ++ show sval ++ "\n"
    Token RightArrow (IdentAttributes modulVal sval) -> "RightArrow " ++ show sval ++ "\n"
    Token Tilde (IdentAttributes modulVal sval) -> "Tilde " ++ show sval ++ "\n"
    Token Bind (IdentAttributes modulVal sval) -> "Bind " ++ show sval ++ "\n"
    Token Select (IdentAttributes modulVal sval) -> "Select " ++ show sval ++ "\n"

-- special identifiers
    Token Id_as (IdentAttributes modulVal sval) -> "Id_as " ++ show sval ++ "\n"
    Token Id_ccall (IdentAttributes modulVal sval) -> "Id_ccall " ++ show sval ++ "\n"
    Token Id_forall (IdentAttributes modulVal sval) -> "Id_forall " ++ show sval ++ "\n"
    Token Id_hiding (IdentAttributes modulVal sval) -> "Id_hiding " ++ show sval ++ "\n"
    Token Id_interface (IdentAttributes modulVal sval) -> "Id_interface " ++ show sval ++ "\n"
    Token Id_primitive (IdentAttributes modulVal sval) -> "Id_primitive " ++ show sval ++ "\n"
    Token Id_qualified (IdentAttributes modulVal sval) -> "Id_qualified " ++ show sval ++ "\n"

-- special operators
    Token SymDot (IdentAttributes modulVal sval) -> "SymDot " ++ show sval ++ "\n"
    Token SymMinus (IdentAttributes modulVal sval) -> "SymMinus " ++ show sval ++ "\n"
    Token SymMinusDot (IdentAttributes modulVal sval) -> "SymMinusDot " ++ show sval ++ "\n"

-- pragmas
    Token PragmaLanguage NoAttributes -> "PragmaLanguage\n"
    Token PragmaOptions (OptionsAttributes toolVal toolArgs) -> "PragmaOptions " ++ show toolArgs ++ "\n" 
    Token PragmaHiding NoAttributes -> "PragmaHiding\n" 
    Token PragmaEnd NoAttributes -> "PragmaEnd #-}\n" 

-- comments
    Token LineComment (StringAttributes sval original) -> "LineComment " ++ show sval ++ "\n"
    Token NestedComment (StringAttributes sval original) -> "NestedComment " ++ show sval ++ "\n"

-- end-of-file token
    Token EOF NoAttributes -> "EOF \n"

-- else
    _ -> show t ++ "\n"
