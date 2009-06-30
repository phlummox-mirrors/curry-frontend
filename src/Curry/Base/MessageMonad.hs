{-
  The \texttt{MsgMonad} type is used for describing the result of a
  computation that can fail. In contrast to the standard \texttt{Maybe}
  type, its \texttt{Error} case provides for an error message that
  describes the failure.
-}

module Curry.Base.MessageMonad where

import Control.Monad.Error
import Control.Monad.Writer

import Curry.Base.Position

type MsgMonad = ErrorT WarnMsg (Writer [WarnMsg])

data WarnMsg = WarnMsg { warnPos :: Position,
                         warnTxt :: String
                       }
instance Error WarnMsg where
    noMsg = WarnMsg (AST noRef) "Failure"


showError w = "Error: " ++ show (warnPos w) ++ warnTxt w

ok :: MsgMonad a -> a
ok = either (error . showError) id . ignoreWarnings


failWith :: String -> MsgMonad a
failWith = throwError . strMsg


ignoreWarnings = fst . runWriter . runErrorT