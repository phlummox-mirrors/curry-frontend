

import List

test1 = elemIndex 'a' "cab" == Just 1
test2 = elemIndex 'a' "z" == Nothing

test3 = nub [1 :: Int, 2, 3, 1, 2, 4] == [1, 2, 3, 4]

test4 = sort "zydlejhgl" == "deghjllyz"

test5 = maximum "agehp" == 'p'

test6 = sum [1 :: Int, 2, 3] == 6
test7 = product [1 :: Int, 2, 4, 3] == 24

test8 = insert 'f' "abcghi" == "abcfghi"

allTests = [test1, test2, test3, test4, test5, test6, test7, test8]

allCorrect = and allTests

