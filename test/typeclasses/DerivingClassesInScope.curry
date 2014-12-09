
class C a where

class D a where

class E a where

data T a = T a
  deriving (C, DerivingClassesInScope.D, E)