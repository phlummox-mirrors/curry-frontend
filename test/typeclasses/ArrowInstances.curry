

class A a where
  funA :: a -> a

instance (A a, A b) => A (a -> b) where
  funA f = f

instance A Bool where

test = funA (\x -> x :: Bool)

class C a where

instance C ((->) a b) where

-- instance C ((Prelude.->) a b) where

