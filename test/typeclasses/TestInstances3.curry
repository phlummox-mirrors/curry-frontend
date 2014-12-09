

class A a where
class B a where
class C a where
class D a where

data T = T


type X = T

instance A X where

instance A NotExistent where


