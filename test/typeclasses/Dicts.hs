

-- class C a where
--   fun1 :: Ord b => a -> b -> Bool
--   fun2 :: b -> a -> Bool

selFun1 :: (a, b) -> a
selFun1 (x, _) = x

selFun2 :: (a, b) -> b
selFun2 (_, x) = x

-- dictC :: (a -> b -> Bool, b -> a -> Bool)

fInt1 :: Ord b => Int -> b -> Bool
fInt1 = error ""

fInt2 :: b -> Int -> Bool
fInt2 = error ""

fChar1 :: Ord b => Char -> b -> Bool
fChar1 = error ""

fChar2 :: b -> Char -> Bool
fChar2 = error ""

-- instance C Int where
--  fun1 = fInt1
--  fun2 = fInt2

-- instance C Char where
--   fun1 = fChar1
--   fun2 = fChar2

data T a = T a

-- instance Eq a => C (T a) where
--   fun1 = fT1
--   fun2 = fT2

fT1 :: (Eq a, Ord b) => T a -> b -> Bool
fT1 = error ""

fT2 :: Eq a => b -> T a -> Bool
fT2 = error ""

dictCInt :: Ord b => (Int -> b -> Bool, b2 -> Int -> Bool)
dictCInt = (fInt1, fInt2)

dictCChar :: Ord b => (Char -> b -> Bool, b2 -> Char -> Bool)
dictCChar = (fChar1, fChar2)

dictCT :: (Eq a, Ord b) => (T a -> b -> Bool, b2 -> T a -> Bool)
dictCT = (fT1, fT2)

