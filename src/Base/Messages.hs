module Base.Messages
  ( -- * Output of user information
    info, status, putErrLn, putErrsLn
    -- * program abortion
  , abortWith, abortWithMessage, abortWithMessages
  , internalError, errorMessage, errorMessages
    -- * creating messages
  , Message, message, posMessage
  ) where

import Control.Monad (unless)
import System.IO     (hPutStrLn, stderr)
import System.Exit   (exitFailure)

import Curry.Base.Message
  (Message, message, posMessage, ppMessage, ppMessages)

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

-- |Print a list of 'String's as error messages on 'stderr'
-- and abort the program
abortWith :: [String] -> IO a
abortWith errs = putErrsLn errs >> exitFailure

-- |Print a single error message on 'stderr' and abort the program
abortWithMessage :: Message -> IO a
abortWithMessage msg = abortWithMessages [msg]

-- |Print a list of error messages on 'stderr' and abort the program
abortWithMessages :: [Message] -> IO a
abortWithMessages msgs = putErrLn (show $ ppMessages msgs) >> exitFailure

-- |Raise an internal error
internalError :: String -> a
internalError msg = error $ "Internal error: " ++ msg

errorMessage :: Message -> a
errorMessage = error . show . ppMessage

errorMessages :: [Message] -> a
errorMessages = error . show . ppMessages
