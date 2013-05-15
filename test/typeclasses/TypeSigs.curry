
class Eq a where

class A a where
  funA :: Eq bClass => a -> a

test1 :: Bool
test1 = let Just x = let a :: Eq b1 => a -> a
                         a = id in Just True
        in x

test2 :: Bool
test2 = let a :: Eq b2 => a -> a
            a = id in True

test3 :: Bool
test3 = case True of
  True -> let a :: Eq b3 => a -> a
              a = id in True

test4 :: [Bool]
test4 = [True | let a :: Eq b4 => a -> a
                    a = id, 
               _ <- [1, 2]]

test5 :: IO Bool
test5 = do
  let a :: Eq b5 => a -> a
      a = id
  return True

test6 :: Bool
test6 | True = let a :: (Eq b6, Eq b62) => a -> a
                   a = id in True

-- TODO: improve error message by adding position!!!
test7 :: Bool
test7 = (id :: Eq b7 => a -> a) True

test8 :: Bool
test8 = let a :: (Eq b8a, NEq b8a2) => a -> a
            a = id in True &&
        let a :: (Eq b8b) => a -> a
            a = id in True