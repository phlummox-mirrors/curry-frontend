

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

  -- 1: is == here the class method or the predefined ==?
  -- 2: if it's the predefined ==, DO NOT transform it in to sel.Eq.== !!!!
  (/=) x y = not $ (==) x y
  -- (/=) x y = not $ (BugClassMethodsVsPredefinedFuncs.==) x y

  -- (/=) x y = not $ (Prelude.==) x y

test x y = x == y

test2 x y = x Prelude.== y

test3 x y = x BugClassMethodsVsPredefinedFuncs.== y

