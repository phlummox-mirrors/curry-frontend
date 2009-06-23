% -*- LaTeX -*-
% $Id: Combined.lhs,v 1.16 2003/05/07 22:38:37 wlux Exp $
%
% Copyright (c) 1998-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Combined.lhs}
\section{Combined monads}\label{sec:combined-monads}
In this section we introduce combined monads which are parameterized
by another monads. This technique has been explored
in~\cite{KingWadler93:Combining} and very extensively
in~\cite{LiangHudakJones95:ModInterp}. The monad transformers used in
this report are mostly copied from the latter. Some restrictions were
necessary because Haskell~98 does not support multi-parameter type
classes. Especially, we cannot define generic lift operations because
they have to be parameterized over two monad classes. In addition, we
cannot define generic state and environment monad classes.
\begin{verbatim}

> module Combined where

> import Control.Monad
> import Control.Monad.Identity

\end{verbatim}

\subsection{State transformers}
The state transformer monad is defined as usual, except that the
result of the state transformer function is itself a monad. The
unparameterized version is defined by using the identity monad
\texttt{Id} for the base monad.
\begin{verbatim}

> newtype StateT s m a = StateT (s -> m (a,s))
> type St s = StateT s Identity

> unStateT :: StateT s m a -> (s -> m (a,s))
> unStateT (StateT st) = st

> instance Functor f => Functor (StateT s f) where
>   fmap f (StateT st) = StateT (fmap (\(x,s') -> (f x,s')) . st)

> instance Monad m => Monad (StateT s m) where
>   return x = StateT (\s -> return (x,s))
>   StateT st >>= f = StateT (\s -> st s >>= \(x,s') -> unStateT (f x) s')
>   fail msg = StateT (const (fail msg))

> instance MonadPlus m => MonadPlus (StateT s m) where
>   mzero = StateT (const mzero)
>   StateT st `mplus` StateT st' = StateT (\s -> st s `mplus` st' s)

> liftSt :: Monad m => m a -> StateT s m a
> liftSt m = StateT (\s -> m >>= \x -> return (x,s))

> callSt :: Monad m => StateT s m a -> s -> m a
> callSt (StateT st) s = st s >>= return . fst

> runSt :: St s a -> s -> a
> runSt st = runIdentity . callSt st

\end{verbatim}
In addition to the standard monad functions, state monads should
provide means to fetch and change the state. With multi-parameter type
classes, one could use the following class:
\begin{verbatim}

class Monad m => StateMonad s m where
  update :: (s -> s) -> m s
  fetch :: m s
  change :: s -> m s

  fetch = update id
  change = update . const

instance Monad m => StateMonad s (StateT s m) where
  update f = StateT (\s -> return (s,f s))

\end{verbatim}
Unfortunately multi-parameter type classes are not available in
Haskell~98. Therefore we define the corresponding instance functions
for each state monad class separately. Here are the functions for the
state transformers.
\begin{verbatim}

> updateSt :: Monad m => (s -> s) -> StateT s m s
> updateSt f = StateT (\s -> return (s,f s))

> updateSt_ :: Monad m => (s -> s) -> StateT s m ()
> updateSt_ f = StateT (\s -> return ((),f s))

> fetchSt :: Monad m => StateT s m s
> fetchSt = updateSt id

> changeSt :: Monad m => s -> StateT s m s
> changeSt = updateSt . const

\end{verbatim}
Currying and uncurrying for state monads has been implemented
in~\cite{Fokker95:JPEG}. Here we extend this implementation to the
parametric monad classes.
\begin{verbatim}

> stCurry :: Monad m => StateT (s,t) m a -> t -> StateT s m (t,a)
> stCurry (StateT st) t =
>   StateT (\s -> st (s,t) >>= \(x,(s',t')) -> return ((t',x),s'))

> stUncurry :: Monad m => (t -> StateT s m (t,a)) -> StateT (s,t) m a
> stUncurry f =
>   StateT (\(s,t) -> let (StateT st) = f t
>                     in st s >>= \((t',x),s') -> return (x,(s',t')))

\end{verbatim}
\subsection{Environment monad}
A variant of the state transformer monad is the environment monad
which is also known as (state) reader monad.
\begin{verbatim}

> data ReaderT r m a = ReaderT (r -> m a)
> type Rt r a = ReaderT r Identity a

> unReaderT :: ReaderT r m a -> (r -> m a)
> unReaderT (ReaderT rt) = rt

> instance Functor f => Functor (ReaderT r f) where
>   fmap f (ReaderT rt) = ReaderT (fmap f . rt)

> instance Monad m => Monad (ReaderT r m) where
>   return x = ReaderT (\_ -> return x)
>   ReaderT rt >>= f = ReaderT (\r -> rt r >>= \x -> unReaderT (f x) r)
>   fail msg = ReaderT (const (fail msg))

> instance MonadPlus m => MonadPlus (ReaderT r m) where
>   mzero = ReaderT (\_ -> mzero)
>   ReaderT rt `mplus` ReaderT rt' = ReaderT (\r -> rt r `mplus` rt' r)

> liftRt :: Monad m => m a -> ReaderT r m a
> liftRt m = ReaderT (\_ -> m)

> callRt :: ReaderT r m a -> r -> m a
> callRt (ReaderT rt) r = rt r

> runRt :: Rt r a -> r -> a
> runRt rt = runIdentity . callRt rt

> envRt :: Monad m => ReaderT r m r
> envRt = ReaderT return 

\end{verbatim}
Currying can also be applied to state reader monads.
\begin{verbatim}

> rtCurry :: Monad m => ReaderT (r,t) m a -> t -> ReaderT r m a
> rtCurry (ReaderT rt) t = ReaderT (\r -> rt (r,t))

> rtUncurry :: Monad m => (t -> ReaderT r m a) -> ReaderT (r,t) m a
> rtUncurry f = ReaderT (\(r,t) -> let (ReaderT rt) = f t in rt r)

\end{verbatim}
A state reader transformer can be transformed trivially into a state
transformer monad. This is handled by the combinator \texttt{ro}.
\begin{verbatim}

ro :: Monad m => ReaderT r m a -> StateT r m a
ro (ReaderT rt) = StateT (\s -> rt s >>= \x -> return (x,s))

\end{verbatim}
