
test1 = take 10 [1 :: Int .. ] == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
test2 = [1 :: Int .. 3] == [1, 2 , 3]
test3 = [1 :: Int, 4 .. 10] == [1, 4, 7, 10]
test4 = take 5 [0 :: Int, 2 ..] == [0, 2, 4, 6, 8]

test5 = take 3 ['a' .. ] == "abc"
test6 = take 3 ['a', 'c' ..] == "ace"
test7 = ['a' .. 'e'] == "abcde"
test8 = ['a', 'c' .. 'g'] == "aceg"

data T = T1 | T2 | T3 | T4 | T5 | T6 | T7 | T8
  deriving (Eq, Enum)

test9 = [T3 ..] == [T3, T4, T5, T6, T7, T8]
test10 = [T3, T5 ..] == [T3, T5, T7]
test11 = [T1 .. T4] == [T1, T2, T3, T4]
test12 = [T1, T3 .. T7] == [T1, T3, T5, T7]
test13 = [T1, T3 .. T8] == [T1, T3, T5, T7]

test14 = [T5, T4 ..] == [T5, T4, T3, T2, T1]
test15 = [T8, T6 .. T1] == [T8, T6, T4, T2]

test16 = [False ..] == [False, True]
test17 = [True, False ..] == [True, False]

test18 = take 4 ['c', 'c' ..] == "cccc"
test19 = take 4 ['c', 'c' .. 'z'] == "cccc"

allTests = [test1, test2, test3, test4, test5, test6, test7, test8, test9,
  test10, test11, test12, test13, test14, test15, test16, test17, test18, 
  test19]

allCorrect = and allTests

