
class F a where
class D a where
class G a where

class (F a, G a) => E a where

class (D a) => A a where
class (D a, E a) => B a where

class (A a, B a) => C a where

