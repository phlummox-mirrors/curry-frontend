
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



testA1 x = fun x && testA2 x

testA2 x = fun3 x x && testA1 x


testB1 x = testA1 x && testA2 x


{-
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
