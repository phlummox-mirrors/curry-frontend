

test1 = 1
test2 = 1.0

test3 = 1 + 2
test4 = 2.0 + 3.0

test5 = 1 + 2.0

test6 x = x + 1

test7 = 1 - 4

test8 = 3.34 * 2.17

test9 = 7 `div` 3

test10 = 7 `mod` 3

test1a = (test1 :: Int) == 1
test1b = (test1 :: Float) == (1 :: Float)
test2a = (test2 :: Float) == (1.0 :: Float)

test8a = test8 :: Float

test9a = (test9 :: Int) == 2

test10a = (test10 :: Int) == 1

test11 :: Int -> Char
test11 1 = 'a'
test11 2 = 'b'

test11a = test11 1 == 'a'
test11b = test11 2 == 'b'

test12 :: Float -> Char
test12 1.0 = 'a'
test12 2.0 = 'b'

test12a = test12 1.0 == 'a'
test12b = test12 2.0 == 'b'

allTests = [test1a, test1b, test2a, test9a, test10a, test11a, test11b, 
            test12a, test12b]


allCorrect = and allTests
