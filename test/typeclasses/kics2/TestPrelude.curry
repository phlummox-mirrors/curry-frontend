
module TestPrelude where

import Prelude ()
import TCPrelude

import Assertion

-- --------------------------------------------------------------------------
-- Eq class
-- --------------------------------------------------------------------------

test1a = 1 /= 2
test2a = 1 == 1
test3a = 'c' == 'c'
test4a = 'c' /= 'd'

test5 = ['a'] == ['a']
test6 = ['a', 'b'] /= ['c']

test7 = [('a', 1.0)] == [('a', 1.0)]

test8 = [('a', Just 5)] == [('a', Just 5)]

test9 = 5 `elem` [1, 2, 3, 4, 5]

test10 = 5 `notElem` [] && 5 `notElem` [1, 2, 3]

test11 = lookup 3 [(4, 'a'), (3, 'b')] == Just 'b'
test12 = lookup 42 [(4, 'a'), (3, 'b')] == Nothing

-- --------------------------------------------------------------------------
-- Ord class
-- --------------------------------------------------------------------------

test13 = 1 < 2
test14 = 1 <= 2
test15 = 2 > 1
test16 = 2 >= 1
test17 = compare 1 2 == LT
test18 = compare 2 2 == EQ
test19 = compare 3 2 == GT

test20 = 'a' < 'b'
test21 = [] < [1]
test22 = (1, 2) < (3, 4)
test23 = (1, 2) < (1, 3)
test24 = [3] > []
test25 = [3, 2, 4] < [3, 2, 5]

test26 = Nothing < Just 1
test27 = Just 1 < Just 2
test28 = Just 1 <= Just 1

test29 = 1.0 < 2.0
test30 = False < True

test31 = [3, 2, 4] <= [3, 2, 5]
test32 = [3, 2, 4] <= [3, 2, 4]

-- --------------------------------------------------------------------------
-- Show class
-- --------------------------------------------------------------------------

test33 = show 5 == "5"
test34 = show 'a' == "\'a\'"
test35 = show "abcd" == "\"abcd\""
test36 = show (5, True) == "(5,True)"
test37 = show (5, True, 'a') == "(5,True,\'a\')"
test38 = show [5, 6, 42] == "[5,6,42]"
test39 = show 1.0 == "1.0"
test40 = show [Just 1, Nothing] == "[Just 1,Nothing]"
test41 = show (Just (Just 3)) == "Just (Just 3)"


-- --------------------------------------------------------------------------
-- all together
-- --------------------------------------------------------------------------

allTests = [test1a, test2a, test3a, test4a, test5, test6, test7, test8, test9
  , test10, test11, test12, test13, test14, test15, test16, test17, test18
  , test19, test20, test21, test22, test23, test24, test25, test26, test27
  , test28, test29, test30, test31, test32, test33, test34, test35, test36
  , test37, test38, test39, test40, test41]

allCorrect = and allTests

test = assertTrue "allCorrect" allCorrect
