

import Prelude ()
import qualified TCPrelude as TCP

class C a where
  funC :: a -> a

class C a => D a where
  funD :: a -> a

class D a => E a where
  funE :: a -> a

