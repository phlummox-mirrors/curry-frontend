
module HidingClasses (C, D, E) where

class C a where
class C a => D a where
class D a => E a where

