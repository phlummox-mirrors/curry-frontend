

class A a where
  (===) :: a -> a -> Bool

instance A Bool where
  x === y = x

-- infix apply

test1 x y = x === y

test3 = True === False


-- left sections

test5 x y = (x ===) y

test7 = (True ===) False

-- right sections

test9 x y = (=== y) x

test11 = (=== False) True

