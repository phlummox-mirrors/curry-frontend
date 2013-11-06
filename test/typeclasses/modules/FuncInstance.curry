
module FuncInstance where

class C a where

instance C ((->) a b) where
  