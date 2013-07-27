
module AsImportUse (AI.C(..)) where

import AsImport as AI (C(..)) 

class AI.C a => D a where
  funD :: a -> Char
  
test x = AI.funC x

