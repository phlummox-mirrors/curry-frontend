module Base.Messages
  ( -- * Output of user information
    info, status, warn, putErrLn, putErrsLn
    -- * program abortion
  , abortWith, abortWithMessage, abortWithMessages
  , internalError, errorMessage, errorMessages
    -- * creating messages
  , Message, message, posMessage
  , MonadIO (..), CYIO, CYT, left, right, runEitherCYIO
  ) where

import Control.Monad (unless, when)
import Control.Monad.IO.Class
import Control.Monad.Trans.Either
import Data.List     (sort)
import System.IO     (hPutStrLn, stderr)
import System.Exit   (exitFailure)

import Curry.Base.Message hiding (warn)
import CompilerOpts (Options (..), Verbosity (..))

type CYT m a = EitherT [Message] m a

type CYIO a = EitherT [Message] IO a

runEitherCYIO :: CYIO a -> IO a
runEitherCYIO act = do
  res <- runEitherT act
  case res of
    Left errs -> abortWithMessages errs
    Right val -> return val

info :: MonadIO m => Options -> String -> m ()
info opts msg = unless (optVerbosity opts < VerbInfo) (putMsg msg)

status :: MonadIO m => Options -> String -> m ()
status opts msg = unless (optVerbosity opts < VerbStatus) (putMsg msg)

warn :: MonadIO m => Options -> [Message] -> m ()
warn opts msgs = when (optWarn opts && not (null msgs)) $ do
  liftIO $ putErrLn (show $ ppMessages ppWarning $ sort msgs)
  when (optWarnAsError opts) $ liftIO $ do
    putErrLn "Failed due to -Werror"
    exitFailure

-- |Print a message on 'stdout'
putMsg :: MonadIO m => String -> m ()
putMsg msg = liftIO $ putStrLn $ msg ++ " ..."

-- |Print an error message on 'stderr'
putErrLn :: MonadIO m => String -> m ()
putErrLn = liftIO . hPutStrLn stderr

-- |Print a list of error messages on 'stderr'
putErrsLn :: MonadIO m => [String] -> m ()
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
