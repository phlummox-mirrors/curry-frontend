
module DuplicateHiddenClasses2 (E(..)) where

class C a where
  funC2 :: a -> a -> Bool

class C a => E a
