module Base.Messages
  ( -- * Output of user information
    info, status
    -- * Error messages
  , putErrLn, putErrsLn
    -- * program abortion
  , abortWith, internalError, errorAt, errorAt', errorMessage, errorMessages
    -- * creating messages
  , Message, toMessage, posErr, qposErr, mposErr
  ) where

import Control.Monad (unless)
import System.IO (hPutStrLn, stderr)
import System.Exit (ExitCode (..), exitWith)

import Curry.Base.Ident (ModuleIdent (..), Ident (..), QualIdent
  , positionOfQualIdent)
import Curry.Base.MessageMonad (Message, toMessage)
import Curry.Base.Position (Position)

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

-- |Raise an error for a given position
errorAt :: Position -> String -> a
errorAt p msg = error ('\n' : (show $ toMessage p msg))

-- |Raise an error for a given position, uncurried
errorAt' :: (Position, String) -> a
errorAt' = uncurry errorAt

errorMessage :: Message -> a
errorMessage = error . show

errorMessages :: [Message] -> a
errorMessages = error . unlines . map show

posErr :: Ident -> String -> Message
posErr i errMsg = toMessage (positionOfIdent i) errMsg

qposErr :: QualIdent -> String -> Message
qposErr i errMsg = toMessage (positionOfQualIdent i) errMsg

mposErr :: ModuleIdent -> String -> Message
mposErr m errMsg = toMessage (positionOfModuleIdent m) errMsg
