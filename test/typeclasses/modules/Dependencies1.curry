
module Dependencies1 (B1, D2, C2, A7) where

class A1 a where

class A1 a => B1 a where

-- ------------------------------

class A2 a where

class A2 a => B2 a where

class B2 a => C2 a where

class C2 a => D2 a where

-- ------------------------------

class A3 a where

instance A3 Bool where

-- ------------------------------

class A4 a where
class B4 a where
class C4 a where

instance (A4 a, B4 a) => C4 (Maybe a) where

-- ------------------------------

class A5 a where

class A5 a => B5 a where

class B5 a => C5 a where

class C5 a => D5 a where

instance A5 Bool where
instance B5 Bool where
instance C5 Bool where
instance D5 Bool where

-- ------------------------------

class A6 a where

class A6 a => B6 a where

class B6 a => C6 a where

class C6 a => D6 a where

class E6 a where

instance D6 a => E6 (Maybe a) where

-- ------------------------------

class Orphan a where

-- ------------------------------

class A7 a where

  