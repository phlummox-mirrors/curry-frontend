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
import Control.Monad.Trans.Either

import Data.Maybe            (fromMaybe, isJust)
import System.FilePath       ((</>), dropFileName, takeBaseName)

import Curry.Base.Ident      (QualIdent (..), unqualify)
import Curry.Base.Pretty     (text)
import Curry.Files.PathUtils (readModule, lookupCurryFile)
import Curry.Syntax          (Module, lexSource)

import Html.SyntaxColoring

import Base.Messages
import CompilerOpts          (Options (..))
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
  srcFile <- liftIO $ lookupCurryFile (optImportPaths opts) f
  program <- filename2program opts (fromMaybe f srcFile)
  liftIO $ writeFile outFile (program2html baseName program)

-- @param importpaths
-- @param filename
-- @return program
filename2program :: Options -> String -> CYIO [Code]
filename2program opts f = do
  mbModule <- liftIO $ readModule f
  case mbModule of
    Nothing  -> left [message $ text $ "Missing file: " ++ f]
    Just src -> do
      case lexSource f src of
        Left  err  -> left [err]
        Right toks -> do
          typed <- fullParse opts f src
          return (genProgram typed toks)

-- |Return the syntax tree of the source program 'src' (type 'Module'; see
-- Module "CurrySyntax").after inferring the types of identifiers.
-- 'fullParse' always searches for standard Curry libraries in the path
-- defined in the
-- environment variable "PAKCSLIBPATH". Additional search paths can
-- be defined using the argument 'paths'.
fullParse :: Options -> FilePath -> String -> CYIO Module
fullParse opts fn _ = do
  buildCurry (opts { optTargetTypes = []}) fn
  (env, mdl) <- loadAndCheckModule opts fn
  return (fst $ qual opts env mdl)

-- generates htmlcode with syntax highlighting
-- @param modulname
-- @param a program
-- @return HTMLcode
program2html :: String -> [Code] -> String
program2html modulname codes = unlines
  [ "<!DOCTYPE html>"
  , "<html>", "<head>", "<title>Module " ++ modulname ++ "</title>"
  , "<link rel=\"stylesheet\" type=\"text/css\" href=\"currydoc.css\"/>"
  , "</head>"
  , "<body style=\"font-family:'Courier New', Arial;\">"
  , "<table><tbody><tr>"
  , "<td class=\"linenumbers\"><pre>" ++ lineHtml ++ "</pre></td>"
  , "<td class=\"sourcecode\"><pre>" ++ codeHtml ++ "</pre></td>"
  , "</tr></tbody></table>"
  , "</body>"
  , "</html>"
  ]
  where
  lineHtml = unlines $ map show [1 .. length (lines codeHtml)]
  codeHtml = concatMap code2html codes

code2html :: Code -> String
code2html code@(Commentary _) =
  spanTag (code2class code) (replace '<' "<span>&lt</span>" (code2string code))
code2html c
  | isCall c  = maybe tag (addHtmlLink   tag) (getQualIdent c)
  | isDecl c  = maybe tag (addHtmlAnchor tag) (getQualIdent c)
  | otherwise = tag
  where tag = spanTag (code2class c) (htmlQuote (code2string c))

spanTag :: String -> String -> String
spanTag [] str = str
spanTag cl str = "<span class=\"" ++ cl ++ "\">" ++ str ++ "</span>"

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

replace :: Char -> String -> String -> String
replace old new = foldr (\ x -> if x == old then (new ++) else ([x] ++)) ""

addHtmlAnchor :: String -> QualIdent -> String
addHtmlAnchor str qid = "<a name=\"" ++ anchor ++ "\"></a>" ++ str
  where anchor = string2urlencoded (show (unqualify qid))

addHtmlLink :: String -> QualIdent -> String
addHtmlLink str qid =
   let (maybeModIdent, ident) = (qidModule qid, qidIdent qid) in
   "<a href=\"" ++
   maybe "" (\ x -> show x ++ "_curry.html") maybeModIdent ++
   "#" ++
   string2urlencoded (show ident) ++
   "\">" ++
   str ++
   "</a>"

isCall :: Code -> Bool
isCall (TypeCons TypeExport _) = True
isCall (TypeCons TypeImport _) = True
isCall (TypeCons TypeRefer  _) = True
isCall (TypeCons          _ _) = False
isCall (Identifier        _ _) = False
isCall c                       = not (isDecl c) && isJust (getQualIdent c)

isDecl :: Code -> Bool
isDecl (DataCons ConsDeclare _) = True
isDecl (Function FuncDeclare _) = True
isDecl (TypeCons TypeDeclare _) = True
isDecl _                        = False

-- Translates arbitrary strings into equivalent urlencoded string.
string2urlencoded :: String -> String
string2urlencoded = id

htmlQuote :: String -> String
htmlQuote [] = []
htmlQuote (c : cs)
  | c == '<'    = "&lt;"    ++ htmlQuote cs
  | c == '>'    = "&gt;"    ++ htmlQuote cs
  | c == '&'    = "&amp;"   ++ htmlQuote cs
  | c == '"'    = "&quot;"  ++ htmlQuote cs
  | c == '\228' = "&auml;"  ++ htmlQuote cs
  | c == '\246' = "&ouml;"  ++ htmlQuote cs
  | c == '\252' = "&uuml;"  ++ htmlQuote cs
  | c == '\196' = "&Auml;"  ++ htmlQuote cs
  | c == '\214' = "&Ouml;"  ++ htmlQuote cs
  | c == '\220' = "&Uuml;"  ++ htmlQuote cs
  | c == '\223' = "&szlig;" ++ htmlQuote cs
  | otherwise   = c : htmlQuote cs
