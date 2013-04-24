
class G a where
  fun6 :: a -> Bool

testD1 x = testD2 x (error "")
testD2 x y = fun6 y



testE1 x =
  let testF1 x = testF2 x (error "")
      testF2 x y = fun6 y
  in x