
module SyntaxCheck (C(..)) where

class C a where
  funA :: a -> a

test1 x = funA x

test2 x = SyntaxCheck.funA x
