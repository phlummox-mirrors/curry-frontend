

import HidingClasses (E)

import HidingClasses2 (E2)
import HidingClasses3 (E2)

import HidingClasses4 (I) -- hidden H!
import HidingClasses5 (H)

-- test :: C a => a -> a
-- test x = x

-- class C a => F a where
--  funF :: a -> a

data T a = T a 
  
-- instance C a => F (T a) where


-- instance C Bool where

-- instance E Bool where

test2 :: E a => a -> a
test2 x = x

class Here a where
  funHere :: a -> a

test3 :: Here a => a -> a
test3 x = x

test4 :: HidingClassesUse.Here a => a -> a
test4 x = x

-- test5 :: HidingClasses.C a => a -> a
-- test5 x = x

test6 :: HidingClasses.E a => a -> a
test6 x = x

-- test7 :: E2 a => a -> a
-- test7 x = x

test8 :: HidingClasses2.E2 a => a -> a
test8 x = x

test9 :: H a => a -> a
test9 x = x

-- test10 :: HidingClasses4.H a => a -> a
-- test10 x = x

test11 :: HidingClasses5.H a => a -> a
test11 x = x

class H a => J a where

instance H Bool where

