
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

{-
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
  -}


testD1 :: F a => a -> a
testD1 x = fun2 (testD2 x)

testD2 :: G a => a -> a
testD2 x = fun4 (testD1 x)

{-
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
-}

-- ambiguous!
-- testI5 = let x = read "..." in show x
{-
testI6 = let x = read "..." in show (x :: Bool)

testI7 = let x = read "..." in (show :: Bool -> String)

testI8 = read "..."

testI9 = (read "..." :: Bool)

testI10 :: Bool
testI10 = read "..."

testI11 :: a
testI11 = read "..."
 

testI12 :: Show a => a -> String
testI12 a = show a

testI13 :: a -> String
testI13 a = show a

testI14 :: Bool -> String
testI14 a = show a
-}
{-
testJ1 :: (J a, Ord a, Eq a, Show a) => a -> a
testJ1 x = fun2 (testJ2 x)

testJ2 :: (J a, Ord a, Eq a, Show a) => a -> a
testJ2 x = fun4 (testJ1 x)

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
-}