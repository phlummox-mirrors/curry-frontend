

-- class C a where
--   fun1 :: Ord b => a -> b -> Bool
--   fun2 :: b -> a -> Bool
--   fun1 = error "fun1"

class C a

defFun1 :: (C a, Ord b) => a -> b -> Bool
defFun1 = error "fun1"

selFun1 :: (a, b) -> a
selFun1 (x, _) = x

selFun2 :: (a, b) -> b
selFun2 (_, x) = x

-- dictC :: (a -> b -> Bool, b -> a -> Bool)



-- instance C Int where
--  fun1 = fInt1
--  fun2 = fInt2

fInt1 :: Ord b => Int -> b -> Bool
fInt1 = error ""

fInt2 :: b -> Int -> Bool
fInt2 = error ""

dictCInt :: Ord b => (Int -> b -> Bool, b2 -> Int -> Bool)
dictCInt = (fInt1, fInt2)



-- instance C Char where
--   fun1 = fChar1
--   fun2 = fChar2

fChar1 :: Ord b => Char -> b -> Bool
fChar1 = error ""

fChar2 :: b -> Char -> Bool
fChar2 = error ""

dictCChar :: Ord b => (Char -> b -> Bool, b2 -> Char -> Bool)
dictCChar = (fChar1, fChar2)



-- instance Eq a => C (T a) where
--   fun1 = fT1
--   fun2 = fT2

data T a = T a

fT1 :: (Eq a, Ord b) => T a -> b -> Bool
fT1 = error ""

fT2 :: Eq a => b -> T a -> Bool
fT2 = error ""

dictCT :: (Eq a, Ord b) => (T a -> b -> Bool, b2 -> T a -> Bool)
dictCT = (fT1, fT2)


-- instance C (S a) where
--   fun2 = fS2
--   -- fun1 missing

data S a = S a

fS2 :: b -> S a -> Bool
fS2 = error ""


-- -XFlexibleContexts
-- dictCS :: (C (S a), Ord b) => (S a -> b -> Bool, b2 -> S a -> Bool)
-- dictCS = (defFun1, fS2)

dictCS :: (C a, Ord b) => (a -> b -> Bool, b2 -> S a -> Bool)
dictCS = (defFun1, fS2)
