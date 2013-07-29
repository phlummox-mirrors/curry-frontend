
module ClassHierarchy2 where

import ClassHierarchy

class C a => D a where
  funD :: a -> a
