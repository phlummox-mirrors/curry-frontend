

class A a where

class B a where

class E a where

class (A a) => C a where

class (A a, B a, E a) => D a where

class (C a, D a ) => F a where

class (D a) => G a where

class (F a, G a) => H a where

class I a where

class (I a) => J a where

class (J a) => K a where

class M a where

class (K a, M a) => L a where

class N a where

class O a where

data T a = T a

data S a = S a

instance A a => A [a] where

instance B a => B [a] where

instance A a => A (S a) where

data U a = U a

instance B a => A (U a) where

data V a b = V a b

instance (A a, B b) => E (V a b) where

instance E a => E ((->) a b) where


instance (M a, K a) => I ((->) a b) where


instance N a => O (T a) where

instance O a => N (T a) where


instance N a => N (a, b) where

instance N () where

data Q a = Q a

instance N (Q a) where

data R1 = R1
data R2 = R2
data W a = W a

instance N R1 where

instance N a => N (W a) where



class P a where

class P a => R a where

class (P a, R a) => Q a where

