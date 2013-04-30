
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

class I a where
  fun8 :: a -> a

testA1 x = fun x && testA2 x

testA2 x = fun3 x x && testA1 x


testB1 x = testA1 x && testA2 x


{-
-- produces "ambiguous type varialbe" error
testC1 x = fun x && testC2 x

testC2 x = fun3 x x && testC3 x (error "")

testC3 x y = fun5 True && testC1 x && fun6 y
-}


testD1 x y = fun x && testD2 y x

testD2 x y = fun6 y && testD1 y x


testE1 x y = fun x && testE2 y x

testE2 x y = fun6 y && testE1 x y


testF1 x = fun x && testF2 x

testF2 x = testF3 x

testF3 x = testF4 x

testF4 x = testF1 x



testG1 x = fun x && testG2 x

testG2 x =
  let testH1 x = fun x && testH2 x
      testH2 x = fun3 x x && testH1 x
  in fun3 x x && testG1 x
 


testI1 x y = fun x && testI2 x && fun2 y

testI2 x = fun3 x x && testI1 x True


testJ1 x = fun2 (testJ2 x)

testJ2 x =
  let testB1 a = testB2 (fun2 a)
      testB2 b = let testC1 c = testC2 (fun5 c)
                     testC2 d = testC1 (fun8 d)
                 in testB1 (fun4 b)
  in fun4 (testJ1 x)

