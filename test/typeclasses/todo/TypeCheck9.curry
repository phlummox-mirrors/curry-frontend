


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



testA4 :: Int
testA4 = True


-- why here strange error messages?
testF1 :: F a => a -> a
testF1 x = fun2 (testF2 x)

testF2 :: G a => a -> a
testF2 x = fun4 (testF1 x)













