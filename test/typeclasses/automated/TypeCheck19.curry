
data T a b c = T a b c

class C a where
  funC :: a -> a

test1 x y z = funC (T x y z)

test2 x z = funC (T x True z)

test3 x y z = funC (T x (T x y z) z)

