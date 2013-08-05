
module DuplicateClassesUse2Err where

import DuplicateClassesUse

test :: C a => a -> a
test x = x
