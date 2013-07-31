
module DuplicateClassesUse (D(..)) where

import DuplicateClasses1
import DuplicateClasses2

class (DuplicateClasses1.C a, DuplicateClasses2.C a) => D a where
  funD :: a -> a -> Bool
  
