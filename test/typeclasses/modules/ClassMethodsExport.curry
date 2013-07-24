
module ClassMethodsExport
  ( C
  , D (funD1)
  , E (funE1, funE3)
  , F (..)
  , H (funH1)
  ) where

class C a where
  funC1 :: a -> a
  funC2 :: a -> a
  funC3 :: a -> a -> Bool

class D a where
  funD1 :: a -> a
  funD2 :: a -> a
  funD3 :: a -> a -> Bool

class E a where
  funE1 :: a -> a
  funE2 :: a -> a
  funE3 :: a -> a -> Bool

class F a where
  funF1 :: a -> a
  funF2 :: a -> a
  funF3 :: a -> a -> Bool

class G a where
  funG1 :: a -> a

class G a => H a where
  funH1 :: a -> a