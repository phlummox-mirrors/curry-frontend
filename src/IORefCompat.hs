{-# OPTIONS -cpp  #-} 
module IORefCompat (
#if __GLASGOW_HASKELL__ >= 604
  module Data.IORef 
#else
  module IOExts 
#endif
  ) where

-- this module ensures compatibility with new and old ghc versions
-- it is necessary, because the ghc flags do not work properly with 
-- literate style.

#if __GLASGOW_HASKELL__ >= 604
import Data.IORef 
#else
import IOExts 
#endif
