
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a



testLC6 y = [True | let b = fun5 y]
testLC6b y = [True | let a = fun3 y y]


-- testLC7 y = [True | let b x = fun5 y]
-- testLC8 y = [True | let a x = fun3 y y]

testDo15 x y z = do
  let ad = fun3 y y
      bd = fun5 z
      cd v = fun2 v
  return (fun x && ad && fun bd)