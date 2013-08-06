
module AmbigDTypeImport where

import AmbigDType1
import AmbigDType2

-- data A a = A a

class C a where

-- error:
-- instance C A where

-- ok:
instance C AmbigDType1.A where
instance C AmbigDType2.A where

