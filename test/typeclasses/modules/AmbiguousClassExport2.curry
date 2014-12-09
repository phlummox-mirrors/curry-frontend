
module AmbiguousClassExport2 (C(..)) where

import AmbiguousClassExport1

class C a where
  funC :: a -> a -> a
