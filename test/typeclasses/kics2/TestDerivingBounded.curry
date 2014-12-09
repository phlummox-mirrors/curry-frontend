
-- import Assertion

import DerivingBounded

test1 = (minBound :: S) == S1
test2 = (maxBound :: S) == S4

test3 = (minBound :: U Bool) == U False
test4 = (maxBound :: U Bool) == U True

test5 = (minBound :: T Bool Bool Bool) == T False False False False S1 (U False)
test6 = (maxBound :: T Bool Bool Bool) == T True True True True S4 (U True)

allTests = [test1, test2, test3, test4, test5, test6]

allCorrect = and allTests

-- test = assertTrue "allCorrect" allCorrect
