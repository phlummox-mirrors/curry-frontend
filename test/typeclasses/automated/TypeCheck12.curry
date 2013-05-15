
import Prelude hiding (show)

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

class Show a where
  show :: a -> String

class Read a where
  read :: String -> a
  

class (C a, E a) => J a where

class Ord a where
class Eq a where

instance I a => I [a] where

testA1 :: Bool
testA1 = True

-- testA2 :: a
-- testA2 = True

testA3 :: Bool
testA3 = error ""

-- testA4 :: Int
-- testA4 = True


testB1 :: a -> Bool
testB1 x = testB2 x

testB2 :: a -> Bool
testB2 x = testB1 x



testC1 :: a -> Bool
testC1 x = fun2 (testC2 x)

testC2 :: a -> Bool
testC2 x = fun4 (testC1 x)
 


testD1 :: F a => a -> a
testD1 x = fun2 (testD2 x)

testD2 :: G a => a -> a
testD2 x = fun4 (testD1 x)





testE1 x = fun2 (testE2 x)
testE2 x = fun4 (testE1 x)


testF1 :: F a => a -> a
testF1 x = fun2 (testF2 x)

testF2 :: G a => a -> a
testF2 x = fun4 (testF1 x)


testG1 :: C a => a -> a
testG1 x = fun2 (testG2 x)

testG2 :: E a => a -> a
testG2 x = fun4 (testG1 x)


testH1 :: J a => a -> a
testH1 x = fun2 (testH2 x)

testH2 :: J a => a -> a
testH2 x = fun4 (testH1 x)


testI1 = (error "") :: Int
testI2 = (error "") :: Bool

-- testI3 = (1 :: Bool)
-- testI4 = (1 :: a -> Int)

testJ1 :: (J a, Ord a, Eq a, Show a) => a -> a
testJ1 x = fun2 (testJ2 x)

testJ2 :: (J a, Ord a, Eq a, Show a) => a -> a
testJ2 x = fun4 (testJ1 x)

testJ1b :: (J a, Ord a, Eq a, Show a) => a -> b -> a
testJ1b x y = fun2 (testJ2b x y)

testJ2b :: (J a, Ord a, Eq a, Show a) => a -> b -> a
testJ2b x y = fun4 (testJ1b x y)

testK1 :: Eq a => a -> a -> Bool
testK1 x y = [x, x] == [y, y]

testL1 :: (J a, Ord a, Eq a, Show a) => a -> a
testL1 x = fun2 (testL2 x)

testL2 :: (J a) => a -> a
testL2 x = fun4 (testL1 x)

testM1 :: (J a) => a -> a
testM1 x = fun2 (testM2 x)

testM2 :: (J a) => a -> a
testM2 x = fun4 (testM1 x)


testN1 :: (J a, Ord b) => a -> b -> a
testN1 x y = fun2 (testN2 x y)

testN2 :: (J a) => a -> b -> a
testN2 x y = fun4 (testN1 x y)



testO1 :: G a => a -> a
testO1 x = testO2 x

testO2 :: F a => a -> a
testO2 x = testO1 x



testP1 :: a -> a
testP1 x = testP2 x

testP2 :: F a => a -> a
testP2 x = testP1 x


testQ1 :: a -> a
testQ1 x = testQ2 (fun2 x)

testQ2 :: a -> a
testQ2 x = testQ1 x


testR1 :: G a => a -> b
testR1 x = testR2 (fun2 x)

testR2 :: F a => a -> b
testR2 x = testR1 x



testS1 :: G a => a -> b -> c
testS1 x y = testS2 y x

testS2 :: F b => a -> b -> c
testS2 x y = testS1 y x

testT1 :: G a => a -> b -> c
testT1 x y = testT2 x y

testT2 :: F a => a -> b -> c
testT2 x y = testT1 y x





testU1 :: G a => a -> b -> c
testU1 x y = testU2 x y

testU2 :: F a => a -> b -> c
testU2 x y = testU1 y x
  where testU1_1 :: G a => a -> b -> c
        testU1_1 x y = testU2_1 y x

        testU2_1 :: F b => a -> b -> c
        testU2_1 x y = testU1_1 y x
          where testU1_2 :: a -> a
                testU1_2 x = testU2_2 (fun2 x)

                testU2_2 :: a -> a
                testU2_2 x = testU1_2 x






testV1 x y = testV2 x y

testV2 :: F a => a -> b -> c
testV2 x y = testV1 y x


testW1 x y = testW2 x y

testW2 :: F a => a -> b -> c
testW2 x y = testW1 x y

toBool :: a -> Bool
toBool _ = True

testX1 x y = fun x && toBool (testX2 x y)

testX2 :: (F a, G b) => a -> b -> Bool
testX2 x y = testX1 x y 



testY1 :: G a => a -> b -> c
testY1 x y =
  let testY1_1 :: G a => a -> b -> c
      testY1_1 x y = testY2_1 y x

      testY2_1 :: F b => a -> b -> c
      testY2_1 x y = testY1_1 y x
  in testY2 x y

testY2 :: F a => a -> b -> c
testY2 x y = testY1 y x

testZ1 :: a -> Bool
testZ1 x = testZ2 x x

testZ2 :: (F a, G b) => a -> b -> Bool
testZ2 x y = testZ1 x


test2A1 x = fun8 [x]

test2A2 :: (I a) => a -> [a]
test2A2 x = fun8 [x]

test2A3 :: a -> [a]
test2A3 x = fun8 [x]











