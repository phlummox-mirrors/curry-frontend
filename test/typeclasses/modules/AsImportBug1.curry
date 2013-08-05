
module AsImportBug1 where

data T a = T a 

class C a where
  funC :: a -> T a
  
  funC x = T x