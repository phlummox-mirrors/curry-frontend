

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

testA1 x = testA2 x

testA2 x =
  let testB1 a = testB2 (fun2 a)
      testB2 b = let testC1 c = testC2 (fun5 c)
                     testC2 d = testC1 (fun8 d)
                 in testB1 (fun4 b)
  in testA1 x
  


