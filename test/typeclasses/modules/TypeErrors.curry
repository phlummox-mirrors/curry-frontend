

class C a where
  funC :: a -> Int
  
  funC x = 'c'
  
instance C Bool where
  
  funC True = 'c'
  

test :: Int -> Char
test 'c' = 1::Int

test2 :: Int -> Char
test2 1 = 'c'

instance C Int where
  
  funC x = (1::Int) == '2'
