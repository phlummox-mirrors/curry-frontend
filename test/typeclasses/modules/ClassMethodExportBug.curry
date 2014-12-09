

module ClassMethodExportBug 
  (enumFrom
  ) where

import Prelude
  
class Enum a where
  enumFrom       :: a -> [a]
