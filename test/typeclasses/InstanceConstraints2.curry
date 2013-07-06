

class A a where

class A a => B a where

class B a => C a where

data T a = T a

instance A (T a) where

instance B (T a) where

instance C (T a) where

-- -------------------------------
{-
data S a = S a

class K a where

class I a where

instance K c => A (S c) where

instance I b => B (S b) where
-}

-- -------------------------------
{-
class J a where

data U a b = U a b

instance J a => A (U a b) where

instance I c => B (U b c) where

instance K e => C (U d e) where
-}
-- -------------------------------

-- ok
class C2 a where

class C2 a => D2 a where

data V a b = V a b

instance A a => C2 (V a b) where

instance C a => D2 (V a b) where

-- -------------------------------

-- a sample from the haskell report

-- correct:

class Eq a where
class Show a where

class (Eq a, Show a) => Num a

class Foo a where

class Foo a => Bar a where

instance (Eq a, Show a) => Foo [a] where

instance Num a => Bar [a] where

-- not correct:
{-
class Eq' a where
class Show' a where

class (Eq' a, Show' a) => Num' a

class Foo' a where

class Foo' a => Bar' a where

instance Num' a => Foo' [a] where

instance (Eq' a, Show' a) => Bar' [a]
-}
