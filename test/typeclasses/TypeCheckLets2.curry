
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


testG1 x = error ""

testG2 x =
  let testH1 x = fun x -- && testH2 x
      -- testH2 x = asdf
  in testG1 x

  
testN1 x = error ""

testN2 x =
  let testM1 y = fun x -- && testH2 x
      -- testH2 x = asdf
  in testN1 x


-- test g x = g x
  

testI1 x = error ""

testI2 x = testI1 x
  where testJ1 x = fun x -- && testH2 x

testK1 x = error ""

testK2 x = testK1 x
  where testL1 y = fun x -- && testH2 x



testO1 x = error ""
  
testO2 x y = let y1 = fun x; y2 = fun3 y y in testO1 x

testP1 x = testP2 x

testP2 x = let y3 = fun x in testP1 x






testQ1 x = fun x && testQ2 x

testQ2 x =
  let testR1 x = fun x && testR2 x
      testR2 x = fun3 x x && testR1 x
  in fun3 x x && testQ1 x


testS1 x = fun x && testS2 x

testS2 x =
  let testT1 y = fun4 x && testT2 x
      testT2 x = fun7 x x && testT1 x
  in fun3 x x && testS1 x


testU1 x = error ""

testU2 x =
  let testV1 y = fun x && fun3 y y
  in testU1 x



testW1 x = fun x && testW2 x

testW2 x =
  let testR1 x =   let testX1 x = fun x && testX2 x
                       testX2 x = fun3 x x && testX1 x in fun x && testR2 x
      testR2 x = fun3 x x && testR1 x
  in fun3 x x && testW1 x

