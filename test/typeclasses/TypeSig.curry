
import Prelude hiding (show)

class B a where

-- error: 
test1 :: (A a) => a -> a
test1 x = x

test2 :: (B a) => a -> a
test2 x = x

-- error: 
test3 :: (A a, B a) => a -> a
test3 x = x
