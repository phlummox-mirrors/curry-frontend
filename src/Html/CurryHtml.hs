{- |
    Module      :  $Header$
    Description :  Generating HTML documentation
    Copyright   :  (c) 2011 - 2014, Björn Peemöller
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    This module defines a function for generating HTML documentation pages
    for Curry source modules.
-}
module Html.CurryHtml (source2html) where

import Control.Monad.Writer

import Data.List             (mapAccumL)
import Data.Maybe            (fromMaybe, isJust)
import Network.URI           (escapeURIString, isUnreserved)
import System.FilePath       ((</>), dropFileName, joinPath, takeBaseName)

import Curry.Base.Ident      (ModuleIdent (..), QualIdent (..), unqualify)
import Curry.Base.Monad
import Curry.Base.Pretty     (text)
import Curry.Files.Filenames (moduleNameToFile)
import Curry.Files.PathUtils (readModule, lookupCurryFile)
import Curry.Syntax          (Module (..), lexSource)

import Html.SyntaxColoring

import Base.Messages
import CompilerOpts          (Options (..), WarnOpts (..))
import CurryBuilder          (buildCurry)
import Modules               (loadAndCheckModule)
import Transformations       (qual)

-- translate source file into HTML file with syntaxcoloring
-- @param sourcefilename
source2html :: Options -> FilePath -> CYIO ()
source2html opts f = do
  let baseName   = takeBaseName f
      outDir     = fromMaybe (dropFileName f) $ optHtmlDir opts
      outFile    = outDir </> baseName ++ "_curry.html"
  srcFile <- liftIO $ lookupCurryFile ("." : optImportPaths opts) f
  (m, program) <- filename2program opts (fromMaybe f srcFile)
  liftIO $ writeFile outFile (program2html m program)

-- @param importpaths
-- @param filename
-- @return program
filename2program :: Options -> String -> CYIO (ModuleIdent, [Code])
filename2program opts f = do
  mbModule <- liftIO $ readModule f
  case mbModule of
    Nothing  -> failMessages [message $ text $ "Missing file: " ++ f]
    Just src -> do
      toks  <- liftCYM $ lexSource f src
      typed@(Module _ m _ _ _) <- fullParse opts f src
      return (m, genProgram typed toks)

-- |Return the syntax tree of the source program 'src' (type 'Module'; see
-- Module "CurrySyntax").after inferring the types of identifiers.
-- 'fullParse' always searches for standard Curry libraries in the path
-- defined in the
-- environment variable "PAKCSLIBPATH". Additional search paths can
-- be defined using the argument 'paths'.
fullParse :: Options -> FilePath -> String -> CYIO Module
fullParse opts fn _ = do
  buildCurry (opts { optTargetTypes = []}) fn
  (env, mdl) <- loadAndCheckModule opts' fn
  return (fst $ qual opts env mdl)
  where
  opts' = opts { optWarnOpts    = (optWarnOpts opts) { wnWarn = False }
               , optTargetTypes = []
               }

-- generates htmlcode with syntax highlighting
-- @param modulname
-- @param a program
-- @return HTMLcode
program2html :: ModuleIdent -> [Code] -> String
program2html m codes = unlines
  [ "<!DOCTYPE html>"
  , "<html>", "<head>"
  , "<meta http-equiv=\"Content-Type\" content=\"text/html;charset=utf-8\" />"
  , "<title>" ++ titleHtml ++ "</title>"
  , "<link rel=\"stylesheet\" type=\"text/css\" href=\"" ++ styleLink ++ "\"/>"
  , "</head>"
  , "<body>"
  , "<table><tbody><tr>"
  , "<td class=\"linenumbers\"><pre>" ++ lineHtml ++ "</pre></td>"
  , "<td class=\"sourcecode\"><pre>" ++ codeHtml ++ "</pre></td>"
  , "</tr></tbody></table>"
  , "</body>"
  , "</html>"
  ]
  where
  titleHtml = "Module " ++ show m
  styleLink = makeTopPath m </> "currydoc.css"
  lineHtml  = unlines $ map show [1 .. length (lines codeHtml)]
  codeHtml  = concat $ snd $ mapAccumL (code2html m) [] codes

code2html :: ModuleIdent -> [QualIdent] -> Code -> ([QualIdent], String)
code2html m defs c
  | isCall c  = (defs, maybe tag (addHtmlLink m tag) (getQualIdent c))
  | isDecl c  = case getQualIdent c of
      Just i | i `notElem` defs
        -> (i:defs, spanTag (code2class c) (escIdent i) (escCode c))
      _ -> (defs, tag)
  | otherwise = (defs, tag)
  where tag = spanTag (code2class c) "" (escCode c)

escCode :: Code -> String
escCode = htmlQuote . code2string

escIdent :: QualIdent -> String
escIdent = string2urlencoded . show . unqualify

spanTag :: String -> String -> String -> String
spanTag clV idV str
  | null clV && null idV = str
  | otherwise            = "<span" ++ codeclass ++ idValue ++ ">"
                           ++ str ++ "</span>"
  where
  codeclass = if null clV then "" else " class=\"" ++ clV ++ "\""
  idValue   = if null idV then "" else " id=\"" ++ idV ++ "\""

-- which code has which css class
-- @param code
-- @return css class of the code
code2class :: Code -> String
code2class (Space        _) = ""
code2class NewLine          = ""
code2class (Keyword      _) = "keyword"
code2class (Pragma       _) = "pragma"
code2class (Symbol       _) = "symbol"
code2class (TypeCons   _ _) = "type"
code2class (DataCons   _ _) = "cons"
code2class (Label      _ _) = "label"
code2class (Function   _ _) = "func"
code2class (Identifier _ _) = "ident"
code2class (ModuleName   _) = "module"
code2class (Commentary   _) = "comment"
code2class (NumberCode   _) = "number"
code2class (StringCode   _) = "string"
code2class (CharCode     _) = "char"

addHtmlLink :: ModuleIdent -> String -> QualIdent -> String
addHtmlLink m str qid =
  "<a href=\"" ++ modPath ++ "#" ++ fragment  ++ "\">" ++ str ++ "</a>"
  where
  modPath       = maybe "" (makeRelativePath m) mmid
  fragment      = string2urlencoded (show ident)
  (mmid, ident) = (qidModule qid, qidIdent qid)

makeRelativePath :: ModuleIdent -> ModuleIdent -> String
makeRelativePath cur new
  | cur == new = ""
  | otherwise  = makeTopPath cur </> moduleNameToFile new ++ "_curry.html"

makeTopPath :: ModuleIdent -> String
makeTopPath m = joinPath $ replicate (length (midQualifiers m) - 1) ".."

isCall :: Code -> Bool
isCall (TypeCons TypeExport _) = True
isCall (TypeCons TypeImport _) = True
isCall (TypeCons TypeRefer  _) = True
isCall (TypeCons          _ _) = False
isCall (Identifier        _ _) = False
isCall c                       = not (isDecl c) && isJust (getQualIdent c)

isDecl :: Code -> Bool
isDecl (DataCons ConsDeclare  _) = True
isDecl (Function FuncDeclare  _) = True
isDecl (TypeCons TypeDeclare  _) = True
isDecl (Label    LabelDeclare _) = True
isDecl _                         = False

-- Translates arbitrary strings into equivalent urlencoded string.
string2urlencoded :: String -> String
string2urlencoded = escapeURIString isUnreserved

htmlQuote :: String -> String
htmlQuote [] = []
htmlQuote (c : cs)
  | c == '<'  = "&lt;"    ++ htmlQuote cs
  | c == '>'  = "&gt;"    ++ htmlQuote cs
  | c == '&'  = "&amp;"   ++ htmlQuote cs
  | c == '"'  = "&quot;"  ++ htmlQuote cs
  | c == 'ä'  = "&auml;"  ++ htmlQuote cs
  | c == 'ö'  = "&ouml;"  ++ htmlQuote cs
  | c == 'ü'  = "&uuml;"  ++ htmlQuote cs
  | c == 'Ä'  = "&Auml;"  ++ htmlQuote cs
  | c == 'Ö'  = "&Ouml;"  ++ htmlQuote cs
  | c == 'Ü'  = "&Uuml;"  ++ htmlQuote cs
  | c == 'ß'  = "&szlig;" ++ htmlQuote cs
  | otherwise = c : htmlQuote cs
