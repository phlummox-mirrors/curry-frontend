
module DuplicateHiddenClasses1 (D(..)) where

class C a where
  funC1 :: a -> a

class C a => D a
