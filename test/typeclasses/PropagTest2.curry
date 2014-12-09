

class A a where
  funA :: a -> a

instance A Int where
  funA x = x

toBool _ = True
  
test4 x = toBool y
  -- where Just y = Just (funA (y::Int))
  where y = funA (y :: Int)
       --       where y :: Int
       --             y = funA y
