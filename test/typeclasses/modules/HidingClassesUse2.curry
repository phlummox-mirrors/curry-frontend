

import HidingClasses5 (H)

test9 :: H a => a -> a
test9 x = x

-- test10 :: HidingClasses4.H a => a -> a
-- test10 x = x

test11 :: HidingClasses5.H a => a -> a
test11 x = x

class H a => J a where

instance H Bool where

