

class A a where
  ($$$) :: a -> a -> Bool

  x $$$ y = True

class B a where
  (=?=) :: a -> a -> Bool

data C a = C a
  
type C' a = C a
