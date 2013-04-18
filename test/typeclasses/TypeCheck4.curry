
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

testCase x =
  case x of
    True -> fun x
    False -> fun4 x

testCase2 x y z =
  case x of
    1 -> fun2 y
    2 -> fun4 z

testCase3 x =
  case fun x of
    True -> False
    False -> True

testCase4 x y =
  case fun x of
    True -> fun3 y y
    False -> True

testCase5 x =
  case x of
    True -> False
    False -> True

testCase6 x =
  case x of
    True -> fun 'c'

testCase7 x y =
  case x of
    True -> fun 'c'
    False -> fun4 y

testCase8 x y =
  case fun x of
    True -> fun4 'c'
    False -> 'd'

