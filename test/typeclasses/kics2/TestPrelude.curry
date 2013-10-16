
module TestPrelude where

-- import Assertion

-- --------------------------------------------------------------------------
-- Eq class
-- --------------------------------------------------------------------------

test1a = (1 :: Int) /= 2
test2a = (1 :: Int) == 1
test3a = 'c' == 'c'
test4a = 'c' /= 'd'

test5 = ['a'] == ['a']
test6 = ['a', 'b'] /= ['c']

test7 = [('a', 1.0 :: Float)] == [('a', 1.0)]

test8 = [('a', Just (5 :: Int))] == [('a', Just 5)]

test9 = (5 :: Int) `elem` [1, 2, 3, 4, 5]

test10 = (5 :: Int) `notElem` [] && (5 :: Int) `notElem` [1, 2, 3]

test11 = lookup (3 :: Int) [(4, 'a'), (3, 'b')] == Just 'b'
test12 = lookup (42 :: Int) [(4, 'a'), (3, 'b')] == Nothing

-- --------------------------------------------------------------------------
-- Ord class
-- --------------------------------------------------------------------------

test13 = (1 :: Int) < 2
test14 = (1 :: Int) <= 2
test15 = (2 :: Int) > 1
test16 = (2 :: Int) >= 1
test17 = compare (1 :: Int) 2 == LT
test18 = compare (2 :: Int) 2 == EQ
test19 = compare (3 :: Int) 2 == GT

test20 = 'a' < 'b'
test21 = [] < [1 :: Int]
test22 = (1 :: Int, 2 :: Int) < (3, 4)
test23 = (1 :: Int, 2 :: Int) < (1, 3)
test24 = [3 :: Int] > []
test25 = [3 :: Int, 2, 4] < [3, 2, 5]

test26 = Nothing < Just (1 :: Int)
test27 = Just (1 :: Int) < Just 2
test28 = Just (1 :: Int) <= Just 1

test29 = (1.0 :: Float) < 2.0
test30 = False < True

test31 = [3 :: Int, 2, 4] <= [3, 2, 5]
test32 = [3 :: Int, 2, 4] <= [3, 2, 4]

-- --------------------------------------------------------------------------
-- Show class
-- --------------------------------------------------------------------------

test33 = show (5 :: Int) == "5"
test34 = show 'a' == "\'a\'"
test35 = show "abcd" == "\"abcd\""
test36 = show (5 :: Int, True) == "(5,True)"
test37 = show (5 :: Int, True, 'a') == "(5,True,\'a\')"
test38 = show [5 :: Int, 6, 42] == "[5,6,42]"
test39 = show (1.0 :: Float) == "1.0"
test40 = show [Just (1 :: Int), Nothing] == "[Just 1,Nothing]"
test41 = show (Just (Just (3 :: Int))) == "Just (Just 3)"

-- --------------------------------------------------------------------------
-- Enum and bounded classes
-- --------------------------------------------------------------------------

test42 = (minBound :: Bool) == False
test43 = (maxBound :: Bool) == True
test44 = (minBound :: (Bool, Bool, Bool)) == (False, False, False)
test45 = (maxBound :: (Bool, Bool, Bool)) == (True, True, True)
test46 = (minBound :: ()) == ()
test47 = (maxBound :: ()) == ()

test48 = succ False == True
test49 = pred True == False
test50 = toEnum (0 :: Int) == False
test51 = toEnum (1 :: Int) == True

test52 = (minBound :: Ordering) == LT
test53 = (maxBound :: Ordering) == GT
test54 = enumFromTo LT GT == [LT, EQ, GT]

test55 = succ (1 :: Int) == 2
test56 = succ (2 :: Int) == 3
test57 = pred (1 :: Int) == 0
test58 = pred (2 :: Int) == 1

test59 = enumFromTo (1 :: Int) 4 == [1, 2, 3, 4]
test60 = enumFromThenTo (1 :: Int) 3 5 == [1, 3, 5]

test61 = boundedEnumFrom LT == [LT, EQ, GT]
test62 = boundedEnumFrom GT == [GT]

-- --------------------------------------------------------------------------
-- all together
-- --------------------------------------------------------------------------

allTests = [test1a, test2a, test3a, test4a, test5, test6, test7, test8, test9
  , test10, test11, test12, test13, test14, test15, test16, test17, test18
  , test19, test20, test21, test22, test23, test24, test25, test26, test27
  , test28, test29, test30, test31, test32, test33, test34, test35, test36
  , test37, test38, test39, test40, test41, test42, test43, test44, test45
  , test46, test47, test48, test49, test50, test51, test52, test53, test54
  , test55, test56, test57, test58, test59, test60, test61, test62]

allCorrect = and allTests

-- test = assertTrue "allCorrect" allCorrect
