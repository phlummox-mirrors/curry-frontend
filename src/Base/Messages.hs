module Base.Messages
  ( -- * Output of user information
    info, status, warn, putErrLn, putErrsLn
    -- * program abortion
  , abortWith, abortWithMessage, abortWithMessages
  , internalError, errorMessage, errorMessages
    -- * creating messages
  , Message, message, posMessage
  ) where

import Control.Monad (unless, when)
import Data.List     (sort)
import System.IO     (hPutStrLn, stderr)
import System.Exit   (exitFailure)

import Curry.Base.Message hiding (warn)
import CompilerOpts (Options (..), Verbosity (..))

info :: Options -> String -> IO ()
info opts msg = unless (optVerbosity opts < VerbInfo)
                       (putStrLn $ msg ++ " ...")

status :: Options -> String -> IO ()
status opts msg = unless (optVerbosity opts < VerbStatus)
                         (putStrLn $ msg ++ " ...")

warn :: Options -> [Message] -> IO ()
warn opts msgs = when (optWarn opts && not (null msgs)) $ do
  putErrLn (show $ ppMessages ppWarning $ sort msgs)
  when (optWarnAsError opts) $ do
    putErrLn "Failed due to -Werror"
    exitFailure

-- |Print an error message on 'stderr'
putErrLn :: String -> IO ()
putErrLn = hPutStrLn stderr

-- |Print a list of error messages on 'stderr'
putErrsLn :: [String] -> IO ()
putErrsLn = mapM_ putErrLn

-- |Print a list of 'String's as error messages on 'stderr'
-- and abort the program
abortWith :: [String] -> IO a
abortWith errs = unless (null errs) (putErrsLn errs) >> exitFailure

-- |Print a single error message on 'stderr' and abort the program
abortWithMessage :: Message -> IO a
abortWithMessage msg = abortWithMessages [msg]

-- |Print a list of error messages on 'stderr' and abort the program
abortWithMessages :: [Message] -> IO a
abortWithMessages msgs = do
  unless (null msgs) $ putErrLn (show $ ppMessages ppMessage $ sort msgs)
  exitFailure

-- |Raise an internal error
internalError :: String -> a
internalError msg = error $ "Internal error: " ++ msg

errorMessage :: Message -> a
errorMessage = error . show . ppError

errorMessages :: [Message] -> a
errorMessages = error . show . ppMessages ppError . sort
