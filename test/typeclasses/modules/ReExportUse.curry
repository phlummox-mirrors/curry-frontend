

module ReExportUse (T(..), C(..), K(..), L(..), test) where

import ReExport

data K a = K a

test x = T x

class L a where
  funL :: a -> a
  
