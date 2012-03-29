module Base.Messages
  ( -- * Output of user information
    info, status, putErrLn, putErrsLn
    -- * program abortion
  , abortWith, internalError, errorMessage, errorMessages
    -- * creating messages
  , Message, toMessage, posErr, qposErr, mposErr
  ) where

import Control.Monad (unless)
import System.IO (hPutStrLn, stderr)
import System.Exit (ExitCode (..), exitWith)

import Curry.Base.Ident (ModuleIdent (..), Ident (..), QualIdent, qidPosition)
import Curry.Base.MessageMonad (Message, toMessage)

import CompilerOpts (Options (optVerbosity), Verbosity (..))

info :: Options -> String -> IO ()
info opts msg = unless (optVerbosity opts < VerbInfo)
                       (putStrLn $ msg ++ " ...")

status :: Options -> String -> IO ()
status opts msg = unless (optVerbosity opts < VerbStatus)
                         (putStrLn $ msg ++ " ...")

-- |Print an error message on 'stderr'
putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

-- |Print a list of error messages on 'stderr'
putErrsLn :: [String] -> IO ()
putErrsLn = mapM_ putErrLn

-- |Print a list of error messages on 'stderr' and abort the program
abortWith :: [String] -> IO a
abortWith errs = putErrsLn errs >> exitWith (ExitFailure 1)

-- |Raise an internal error
internalError :: String -> a
internalError msg = error $ "Internal error: " ++ msg

errorMessage :: Message -> a
errorMessage = error . show

errorMessages :: [Message] -> a
errorMessages = error . unlines . map show

posErr :: Ident -> String -> Message
posErr i errMsg = toMessage (idPosition i) errMsg

qposErr :: QualIdent -> String -> Message
qposErr i errMsg = toMessage (qidPosition i) errMsg

mposErr :: ModuleIdent -> String -> Message
mposErr m errMsg = toMessage (midPosition m) errMsg
