
class G a where
  fun6 :: a -> Bool

testD1 x = testD2 x (error "")
testD2 x y = fun6 y

