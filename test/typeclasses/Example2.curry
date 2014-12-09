
class Eq a where
  eq :: a -> a -> Bool
  neq :: a -> a -> Bool

  -- neq x y = not $ eq x y

instance Eq Bool where
  eq True True = True
  eq True False = False
  eq False True = False
  eq False False = True


instance Eq a => Eq [a] where
  eq [] [] = True
  eq (x:xs) (y:ys) = eq x y && eq xs ys
  eq [] (_:_) = False
  eq (_:_) [] = False


instance (Eq a, Eq b) => Eq (a, b) where
  eq (x1, y1) (x2, y2) = eq x1 x2 && eq y1 y2
  neq (x1, y1) (x2, y2) = True


test1 = eq True False

test2 = eq [True, True] [False]

test3 = eq [True, True] [True, True]

test4 = eq [(True, True), (False, False)] []

test5 = eq [(True, False), (False, False)] [(True, False), (False, False)]

test6 = eq [[(True, False)]] [[(True, False)]]



test7 = neq True False

test8 = neq [True, True] [False]

test9 = neq [True, True] [True, True]

test10 = neq [(True, True), (False, False)] []

test11 = neq [(True, False), (False, False)] [(True, False), (False, False)]

test12 = neq [[(True, False)]] [[(True, False)]]

