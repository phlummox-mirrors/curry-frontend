
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

{-
testA1 x = fun x && testA2 x

testA2 x =
  let Just x = Just $ fun2 y
      Just y = Just $ fun4 x
  in fun3 x x && testA1 x

 -}

testB1 x =
  let Just y = Just $ fun2 x
  in x


testC1 x =
  let (y, z) = (fun2 x, fun3 x x)
  in x

testD1 x =
  let ('c', 1, y, z) = ('c', 1, fun2 x, fun3 x x)
  in x