
import Prelude ()
import TCPrelude

import DerivingEnum

test1 = (toEnum 0 :: T) == T1
test2 = (toEnum 3 :: T) == T4

test3 = (toEnum 0 :: S) == S1

test4 = fromEnum T1 == 0
test5 = fromEnum T4 == 3
test6 = fromEnum S1 == 0

-- errors
test7 = toEnum 20 :: T
test8 = toEnum 20 :: S

test9 = succ T1 == T2
test10 = succ T3 == T4

test11 = pred T2 == T1
test12 = pred T4 == T3

-- errors
test13 = succ T4
test14 = pred T1
test15 = succ S1
test16 = pred S1


allTests = [test1, test2, test3, test4, test5, test6, test9, test10, test11
           , test12]

allCorrect = and allTests

