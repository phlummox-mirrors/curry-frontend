
-- import Assertion

import DerivingEnum

test1 = (toEnum (0 :: Int) :: T) == T1
test2 = (toEnum (3 :: Int) :: T) == T4

test3 = (toEnum (0 :: Int) :: S) == S1

test4 = fromEnum T1 == 0
test5 = fromEnum T4 == 3
test6 = fromEnum S1 == 0

-- errors
test7 = toEnum (20 :: Int) :: T
test8 = toEnum (20 :: Int) :: S

test9 = succ T1 == T2
test10 = succ T3 == T4

test11 = pred T2 == T1
test12 = pred T4 == T3

-- errors
test13 = succ T4
test14 = pred T1
test15 = succ S1
test16 = pred S1

test17 = enumFrom U1 == [U1, U2, U3, U4, U5, U6, U7, U8]
test17b = enumFrom U5 == [U5, U6, U7, U8]
test18 = enumFromThen U1 U3 == [U1, U3, U5, U7]
test19 = enumFromThen U8 U6 == [U8, U6, U4, U2]
test19b = enumFromThen U6 U5 == [U6, U5, U4, U3, U2, U1]
test20 = enumFromTo U1 U3 == [U1, U2, U3]
test21 = enumFromTo U4 U8 == [U4, U5, U6, U7, U8]
test22 = enumFromThenTo U1 U3 U7 == [U1, U3, U5, U7]
test22b = enumFromThenTo U1 U3 U6 == [U1, U3, U5]
test23 = enumFromThenTo U2 U4 U6 == [U2, U4, U6]
test23b = enumFromThenTo U2 U4 U5 == [U2, U4]
test24 = enumFromThenTo U7 U6 U2 == [U7, U6, U5, U4, U3, U2]

test25 = enumFrom S1 == [S1]
test26 = enumFromTo S1 S1 == [S1]
test27 = enumFromThen S1 S1 /= [S1]
test28 = enumFromThenTo S1 S1 S1 /= [S1]

allTests = [test1, test2, test3, test4, test5, test6, test9, test10, test11
           , test12, test17, test17b, test18, test19, test19b, test20, test21, test22
           , test22b, test23, test23b, test24, test25, test26, test27, test28]

allCorrect = and allTests

-- test = assertTrue "allCorrect" allCorrect
