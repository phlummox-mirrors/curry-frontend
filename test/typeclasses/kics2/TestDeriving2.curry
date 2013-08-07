
import Prelude ()
import TCPrelude

import Deriving2

test1a = (T1 True :: T Bool Bool) <= T1 True
test2a = not ((T1 True :: T Bool Bool) < T1 True)
test3a = T1 True < T2 True
test4 = (T1 False :: T Bool Bool) < T1 True
test5 = T1 True < T3 True
test6 = compare (T1 True :: T Bool Bool) (T1 True) == EQ
test7 = compare (T1 True) (T2 False) == LT
test8 = compare (T2 False) (T1 True) == GT
test9 = min (T1 True) (T2 False) == T1 True
test10 = max (T1 True) (T2 False) == T2 False
test11 = ('a', 1) <= ('a', 1)
test12 = ('a', 2) > ('a', 1)
test13 = ('a', 1) < ('a', 2)
test14 = ('a', 1, 2) < ('a', 1, 3)
test15 = ('a', 1, 2) < ('b', 1, 2)
test16 = ('a', 1, 2) <= ('a', 1, 2)
test17 = S1 True True () <= S1 True True ()
test18 = S1 True True () < S2
test19 = S2 > S1 True True ()
test20 = S1 1 1 1 <= S1 1 1 1
test21 = S1 1 1 1 <  S1 2 1 1
test22 = S1 1 1 1 <  S1 1 2 1
test23 = S1 1 1 1 <  S1 1 1 2
test24 = compare (S1 1 1 1) S2 == LT
test25 = compare S2 (S1 1 1 1) == GT
test26 = compare (S2 :: S () () ()) S2 == EQ
test27 = (S2 :: S () () ()) <= S2
test28 = (S2 :: S () () ()) >= S2
test29 = not $ (S2 :: S () () ()) < S2
test30 = not $ (S2 :: S () () ()) > S2

test31 = U True True > U True False
test32 = U False 0 < U True 0
test33 = U False 0 < U False 1

test34 = C0 <= C0
test35 = not (C0 < C0)
test36 = not (C0 > C0)

test37 = C4 1 1 1 1 <= C4 1 1 1 1
test38 = C4 1 1 1 1 < C4 2 1 1 1
test39 = C4 1 1 1 1 < C4 1 2 1 1
test40 = C4 1 1 1 1 < C4 1 1 2 1
test41 = C4 1 1 1 1 < C4 1 1 1 2

test42 = [] < ['a']
test43 = ['a'] <= ['a']
test44 = not $ ['a'] < ['a']
test45 = ['a'] > []
test46 = ([] :: [Bool]) <= []
test47 = not (([] :: [Bool]) < [])
test48 = not (([] :: [()]) > [])
test49 = [1, 2] <= [1, 2]
test50 = not ([1, 2] < [1, 2])
test51 = not ([1, 2] > [1, 2])
test52 = [1, 2] < [1, 3]
test53 = [1, 2] < [2, 0]
test54 = [1, 2, 3] < [1, 2, 4]
test55 = [1, 2, 3] < [1, 3, 0]
test56 = [1, 2, 3] < [4, 2, 3]



allTests = [test1a, test2a, test3a, test4, test5, test6, test7, test8, test9
           , test10, test11, test12, test13, test14, test15, test16, test17
           , test18, test19, test20, test21, test22, test23, test24, test25
           , test26, test27, test28, test29, test30, test31, test32, test33
           , test34, test35, test36, test37, test38, test39, test40, test41
           , test42, test43, test44, test45, test46, test47, test48, test49
           , test50, test51, test52, test53, test54, test55, test56]

allCorrect = and allTests
