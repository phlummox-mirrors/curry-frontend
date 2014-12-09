
module AsImport where

import qualified AsImportType as AI (T(..))

class C a where
  funC :: a -> AI.T a
  
