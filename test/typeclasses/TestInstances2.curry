

class A a where
class B a where
class C a where
class D a where

data T = T

instance A Int where

instance B Prelude.Int where

instance A T where

instance B TestInstances2.T where
