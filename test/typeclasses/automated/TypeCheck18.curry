
class A a where
  funA :: a -> a

test1 y = y
  where x = funA x

test2 x = y
  where y = funA y

test3 y = y
  where Just x = Just $ funA x

test4 x = y
  where Just y = Just $ funA y

test5 x = 'a'
  where y = funA x

