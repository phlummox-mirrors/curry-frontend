
import Prelude ()
import TCPrelude


test0 = 1
test0b = 1.0

test1 = 1 + 1

test2 = 1.3 + 2.4

test3 = test1 :: Int
test3b = test1 :: Float

test4 x 1 = x

test5 = 1 + 1.3


test6 :: Num a => a -> a
test6 x = x + 1

test7 :: Fractional a => a -> a
test7 x = x + 1.0


test6a = test6 1
test6b = test6 1.2

test7a = test7 1
test7b = test7 1.2
