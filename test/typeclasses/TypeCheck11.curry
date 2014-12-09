

class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

class G a where
  fun6 :: a -> Bool

class H a where
  fun7 :: a -> a -> Bool

data T a b = T a b
  
-- test x y = [Left $ fun4 x, Right $ fun5 y]
  
test15b x y = let  [Left x2, Right x3] =  [Left $ fun4 x, Right $ fun5 y] in (x2, x3)
-- test15b x y = let  [Left x2, Right x3] =  [Left $ fun4 x, Right $ fun5 y] in T x2 x3

-- test15c x y = let x2 = fun4 x; x3 = fun5 y in (x2, x3)

-- test15d x y = let  [Left x2, Right x3] =  [Left $ fun4 x, Right $ fun5 y] in True

-- test15e x y = let  (Left x2, Right x3) =  (Left $ fun4 x, Right $ fun5 y) in (x2, x3)

-- test15f x y = let Left x2 = Left $ fun4 x; Right x3 =  Right $ fun5 y in (x2, x3)
