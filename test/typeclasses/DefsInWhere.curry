
class C a where
  funC :: a -> a

test1 x = test2 x
  where
  test2 :: C a => a -> a
  test2 y = funC y
