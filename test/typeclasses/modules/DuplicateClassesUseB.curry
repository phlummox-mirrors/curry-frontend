
module DuplicateClassesUseB (D(..), C(..)) where

import qualified DuplicateClasses1 
import qualified DuplicateClasses2

class (DuplicateClasses1.C a, DuplicateClasses2.C a) => D a where
  funD :: a -> a -> Bool
  
class C a where
  funC3 :: a -> a -> a
