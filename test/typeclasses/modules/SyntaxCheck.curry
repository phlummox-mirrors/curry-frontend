
module SyntaxCheck (C(..), D(funD1, funD2, funD3, funD4)) where

class C a where
  funA :: a -> a

test1 x = funA x

test2 x = SyntaxCheck.funA x


class D a where
  funD1 :: a -> a
  funD2 :: a -> a -> Bool
  funD3 :: a -> a
  funD4 :: a -> Bool
  funD5 :: a -> a