
class Eq a where
class Show a where

class (Eq a, Show a) => Num a

class Foo a => Bar a where

instance (Eq a, Show a) => Foo [a] where

instance Num a => Bar [a] where


