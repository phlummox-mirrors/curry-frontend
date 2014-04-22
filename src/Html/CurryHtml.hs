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

import Data.Char             (toLower)
import Data.Maybe            (fromMaybe, isJust)

import Curry.Base.Ident      (QualIdent (..), unqualify)
import Curry.Base.Message
import Curry.Base.Pretty     (text)
import Curry.Files.Filenames (dropExtension, takeFileName)
import Curry.Files.PathUtils (readModule, lookupCurryFile)
import Curry.Syntax          (Module, lexSource, parseModule)

import Html.SyntaxColoring

import Base.Messages
import CompilerOpts          (Options(..), TargetType (..), defaultOptions)
import CurryBuilder          (buildCurry)
import Modules               (loadAndCheckModule, checkModuleHeader)

--- translate source file into HTML file with syntaxcoloring
--- @param sourcefilename
source2html :: Options -> FilePath -> CYIO ()
source2html opts f = do
  let baseName   = dropExtension f
      modulname  = takeFileName baseName
      outFile    = baseName ++ "_curry.html"
  srcFile <- liftIO $ lookupCurryFile (optImportPaths opts) f
  program <- filename2program opts (fromMaybe f srcFile)
  liftIO $ writeFile outFile (program2html modulname program)

--- @param importpaths
--- @param filename
--- @return program
filename2program :: Options -> String -> CYIO Program
filename2program opts f = do
  mbModule <- liftIO $ readModule f
  case mbModule of
    Nothing  -> left [message $ text $ "Missing file: " ++ f]
    Just src -> do
      typed   <- liftIO $ fromIO $ fullParse opts f src
      checked <- liftIO $ fromIO $ fullParse (opts { optTargetTypes = [UntypedAbstractCurry]}) f src
      let parsed = parse f src
          lexed  = lexSource f src
      return $ genProgram src [typed, checked, parsed] lexed

{- |Return the result of a syntactical analysis of the source program 'src'.
    The result is the syntax tree of the program (type 'Module'; see Module
    "CurrySyntax").
-}
parse :: FilePath -> String -> MessageM Module
parse fn src = parseModule fn src >>= genCurrySyntax
  where
  genCurrySyntax mod1 = do
    checked <- lift $ runEitherT $ checkModuleHeader defaultOptions fn mod1
    case checked of
      Left hdrErrs -> failWith $ show $ head hdrErrs
      Right mdl    -> return mdl

{- |Return the syntax tree of the source program 'src' (type 'Module'; see
    Module "CurrySyntax").after inferring the types of identifiers.
    'fullParse' always searches for standard Curry libraries in the path
    defined in the
    environment variable "PAKCSLIBPATH". Additional search paths can
    be defined using the argument 'paths'.
-}
fullParse :: Options -> FilePath -> String -> MessageIO Module
fullParse opts fn _ = do
  errs <- liftIO $ makeInterfaces opts fn
  if null errs
    then do
      checked <- liftIO $ runEitherT $ loadAndCheckModule opts fn
      case checked of
        Left errs'      -> failWith $ show $ head errs'
        Right (_, mod') -> return mod'
    else failWith $ show $ head errs

-- Generates interface files for importes modules, if they don't exist or
-- if they are not up-to-date.
makeInterfaces :: Options -> FilePath -> IO [Message]
makeInterfaces opts fn = do
  res <- runEitherT $ buildCurry opts fn
  case res of
    Left  errs -> return errs
    Right _    -> return []


-- generates htmlcode with syntax highlighting
-- @param modulname
-- @param a program
-- @return HTMLcode
program2html :: String -> Program -> String
program2html modulname codes =
  "<html>\n<head>\n<title>Module " ++
  modulname ++
  "</title>\n" ++
  "<link rel=\"stylesheet\" type=\"text/css\" href=\"currydoc.css\">" ++
  "</link>\n</head>\n" ++
  "<body style=\"font-family:'Courier New', Arial;\">\n<pre>\n" ++
  concatMap (code2html True . (\ (_, _, c) -> c)) codes ++
  "<pre>\n</body>\n</html>"

code2html :: Bool -> Code -> String
code2html ownClass code@(CodeWarning _ c) =
  (if ownClass then spanTag (code2class code) else id) (code2html False c)
code2html ownClass code@(Commentary _) =
  (if ownClass then spanTag (code2class code) else id)
    (replace '<' "<span>&lt</span>" (code2string code))
code2html ownClass c
  | isCall c && ownClass = maybe tag (addHtmlLink   tag) (getQualIdent c)
  | isDecl c && ownClass = maybe tag (addHtmlAnchor tag) (getQualIdent c)
  | otherwise            = tag
  where tag = (if ownClass then spanTag (code2class c) else id)
                      (htmlQuote (code2string c))

spanTag :: String -> String -> String
spanTag [] str = str
spanTag cl str = "<span class=\"" ++ cl ++ "\">" ++ str ++ "</span>"

-- which code has which color
-- @param code
-- @return color of the code
code2class :: Code -> String
code2class (Keyword           _) = "keyword"
code2class (Space             _) = ""
code2class NewLine               = ""
code2class (ConstructorName k _) = "constructorname_"  ++ showLower k
code2class (Function        k _) = "function_" ++ showLower k
code2class (ModuleName        _) = "modulename"
code2class (Commentary        _) = "commentary"
code2class (NumberCode        _) = "numbercode"
code2class (StringCode        _) = "stringcode"
code2class (CharCode          _) = "charcode"
code2class (Symbol            _) = "symbol"
code2class (Identifier      k _) = "identifier_" ++ showLower k
code2class (TypeConstructor k _) = "typeconstructor_" ++ showLower k
code2class (CodeWarning     _ _) = "codewarning"
code2class (NotParsed         _) = "notparsed"

showLower :: Show a => a -> String
showLower = map toLower . show

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
isCall (TypeConstructor TypeExport _) = True
isCall (TypeConstructor          _ _) = False
isCall (Identifier               _ _) = False
isCall code = not (isDecl code) && isJust (getQualIdent code)

isDecl :: Code -> Bool
isDecl (ConstructorName ConstrDecla _) = True
isDecl (Function FunDecl            _) = True
isDecl (TypeConstructor TypeDecla   _) = True
isDecl _                               = False

-- Translates arbitrary strings into equivalent urlencoded string.
string2urlencoded :: String -> String
string2urlencoded = id
{-
string2urlencoded [] = []
string2urlencoded (c:cs)
  | isAlphaNum c = c : string2urlencoded cs
  | c == ' '     = '+' : string2urlencoded cs
  | otherwise = show (ord c) ++ (if null cs then "" else ".") ++ string2urlencoded cs
-}

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
