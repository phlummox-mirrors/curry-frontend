
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

-- instance C Bool where

-- instance E Bool where

instance C (Prelude.Int) where

testC1 :: a -> Bool
testC1 x = fun2 (testC2 x)

testC2 :: a -> Bool
testC2 x = fun4 (testC1 x)

testD1 :: Char -> Char
testD1 x = fun2 x

testE1 :: Int -> Int
testE1 x = fun2 x
