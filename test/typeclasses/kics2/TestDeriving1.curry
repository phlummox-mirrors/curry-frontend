
import Prelude ()
import TCPrelude

import Deriving1

import Assertion

test1a = (T1 False :: T Bool Bool) == T1 False
test2a = (T1 False :: T Bool Bool) /= T1 True
test3a = (T1 True :: T Bool Bool) /= T2 False
test4 = (T3 4 :: T Bool Int) == T3 4
test5 = (T3 4 :: T Bool Int) /= T3 3
test6 = (T1 () :: T () ()) /= T2 ()
test7 = (T1 () :: T () ()) /= T3 ()
test8 = (T2 () :: T () ()) /= T1 ()
test9 = (T2 () :: T () ()) /= T3 ()
test10 = (T3 () :: T () ()) /= T1 ()
test11 = (T3 () :: T () ()) /= T2 ()
test12 = (T1 True :: T Bool Bool) == T1 True
test13 = (T1 False :: T Bool Bool) /= T1 True
test14 = (T2 True :: T Bool Bool) == T2 True
test14b = (T3 True :: T Bool Bool) == T3 True

test15 = S1 True 1 'a' == S1 True 1 'a'
test16 = S1 True 1 'a' /= S1 True 1 'b'
test17 = S1 True 1 'a' /= S1 True 2 'a'
test18 = S1 True 1 'a' /= S1 False 1 'a'
test19 = S1 True 1 'a' /= S2
test20 = S2 /= S1 True 1 'a'
test21 = (S2 :: S () () ()) == S2
test22 = (S2 :: S Float Int Bool) == S2

test23 = U True True == U True True
test24 = U True 2 == U True 2
test25 = U True 2 /= U False 2
test26 = U True 2 /= U True 3

test27 = V 42 == V 42
test28 = V 'c' /= V 'd'

test29 = W (T1 True) (S1 False 2 True) (U False False) == W (T1 True) (S1 False 2 True) (U False False)
test30 = W (T1 True) (S1 False 2 True) (U False False) /= W (T1 True) (S1 False 1 True) (U False False)
test30b = W (T2 3) (S1 False 2 True) (U False False)   /= W (T1 True) (S1 False 2 True) (U False False)

test31 = True :=: 3 == True :=: 3
test32 = True :=: 4 /= True :=: 3

test33 = Y1 True 1 == Y1 True 1
test34 = Y1 True 1 /= Y2 False

allTests = [test1a, test2a, test3a, test4, test5, test6, test7, test8, test9
           , test10, test11, test12, test13, test14, test14b, test15, test16
           , test17, test18, test19, test20, test21, test22, test23, test24
           , test25, test26, test27, test28, test29, test30, test30b, test31
           , test32, test33, test34]

allCorrect = and allTests

test = assertTrue "allCorrect" allCorrect
