
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


test y = let f x = fun2 x in f
test' y = let f x = fun2 y in f
test'' y = let Just x = Just $ fun2 y in x

testA1 x = error ""

testA2 x =
  let testB1 x = fun x
  in testA1 x


-- difference to haskell!
testC1 x = error ""

testC2 x =
  let testD1 y = fun x
  in testC1 x

testE1 x = error ""

testE2 x = testE1 x
  where testF1 x = fun x

  
testG1 x = error ""

testG2 x = testG1 x
  where testH1 y = fun x



testI1 x = error ""

-- difference to haskell!
testI2 x y = let y1 = fun x; y2 = fun3 y y in testI1 x


testJ1 x = testJ2 x

testJ2 x = let y3 = fun x in testJ1 x


testJ1b x = testJ2b x
testJ2b x = let y = fun2 x in testJ1b y

testJ1c x = testJ2c x
testJ2c x = let f1 x = fun2 (f2 x); f2 x = fun4 (f1 x) in testJ1c (f1 x)


testK1 x = fun x && testK2 x

testK2 x =
  let testL1 x = fun x && testL2 x
      testL2 x = fun3 x x && testL1 x
  in fun3 x x && testK1 x


testM1 x = fun x && testM2 x

testM2 x =
  let testN1 y = fun4 x && testN2 x
      testN2 x = fun7 x x && testN1 x
  in fun3 x x && testM1 x


testO1 x = error ""

testO2 x =
  let testP1 y = fun x && fun3 y y
  in testO1 x



testQ1 x = fun x && testQ2 x

testQ2 x =
  let testR1 x =   let testS1 x = fun x && testS2 x
                       testS2 x = fun3 x x && testS1 x in fun x && testR2 x
      testR2 x = fun3 x x && testR1 x
  in fun3 x x && testQ1 x

