
module B where

import A

class B1 a where
  funB1 :: a

class A1 a => B2 a where
  funB2 :: a
