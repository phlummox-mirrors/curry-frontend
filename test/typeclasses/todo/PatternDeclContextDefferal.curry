
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

class G a where
  fun6 :: a -> Bool

class H a where
  fun7 :: a -> a -> Bool

class I a where
  fun8 :: a -> a

-- x2/x3 get too many contexts
test15b x y = let  [Left x2, Right x3] =  [Left $ fun4 x, Right $ fun5 y] in (x2, x3)

