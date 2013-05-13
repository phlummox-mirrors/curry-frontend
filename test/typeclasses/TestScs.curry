

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

