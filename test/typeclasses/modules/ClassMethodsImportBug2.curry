
module ClassMethodsImportBug2 (C(..), D(..)) where

import ClassMethodsImportBug

class C a => D a where
  funD :: a -> a
