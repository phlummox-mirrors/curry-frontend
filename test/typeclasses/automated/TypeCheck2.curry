
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

fun3b :: D a => a -> b -> Bool
fun3b = error ""

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a


testA1 x = let y = fun 'a' in y

testA2 x = y
  where y = fun 'a'

testA3 x = let y = fun x in y

testA4 x = y
  where y = fun x


  

testB1 x z = let y = fun x in z

testB2 x z = let y = fun x in y


testB3 x z = let y = fun x && fun3 x x in (x, y)

testB3b x z = let y = fun x && fun3 x x in x
testB3c x z = let y = fun x && fun3 x x in y

testB4 x y = let x' = fun x
                 y' = fun y
             in (x', y')

testB5 x y = let x' = fun x
                 y' = fun3 y y
             in (x', y')

testB6 x y = let x' = fun x
                 y' = fun x
              in (x', y')

testB7 x = let x' = let x'' = fun x in x'' in x'

testB8 x = let y = 'a' : x in y
testB8b x = let y = 'a' : fun2 x in y
testB8c x z = let y = fun4 x : fun2 z in y

testB9 x = let y = fun 'a' in fun3 x x && y

testB10 x y = let x' = fun x
                  y' = fun y
               in True

testB11 x y = let x' = fun x
                  y' = fun y
               in x'

testB12 x y = let x' = fun x
                  y' = fun y
               in y'

testB13 x y = let x' = fun x
                  y' = fun y
               in (x', y')


testC1 = let x' = fun4 y'
             y' = fun5 x'
         in x'

testC1b = let x' = fun4 y'
              y' = fun5 x'
          in y'

-- different types as Haskell!!
testC1c = let x' = fun4 y'
              y' = fun5 x'
          in (x', y')

testC1d = let x' = y'
              y' = x'
          in (x', y')



testD1 z =
  let b = fun5 z
  in b


testD2 x y z =
  let a = fun3 y y
      b = fun5 z
  in fun x && a && fun b

testD3 x y z =
  fun x && a && fun b
  where a = fun3 y y
        b = fun5 z
