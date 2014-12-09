
import BugClassMethodsAndTopLevelFuns1

class C a where
  test1 :: a -> a -> a -> Bool

allTests = [test1]

allCorrect = and allTests
