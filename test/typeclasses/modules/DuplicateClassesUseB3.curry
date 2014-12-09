
module DuplicateClassesUseB3 where

import DuplicateClassesUseB

test :: C a => a -> a
test x = x

  