
module DefaultMethods where

class C a where
  funA :: a -> a
  funB :: a -> a
  funC :: a -> a

  funA x = x

  funC x = x

class D a where
  ($$$) :: a -> a -> Bool

  x $$$ y = True

