
module AmbigDTypeImport where

import Test1
import Test2

-- data A a = A a

class C a where

-- error:
-- instance C A where

-- ok:
instance C Test1.A where
instance C Test2.A where

