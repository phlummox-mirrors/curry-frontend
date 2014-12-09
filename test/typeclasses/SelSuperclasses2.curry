
class F a where
  funF :: a
  
class D a where
  funD :: a
  
class G a where
  funG :: a

class (F a, G a) => E a where
  funE :: a

class (D a) => A a where
  funA :: a
  
class (D a, E a) => B a where
  funB :: a

class (A a, B a) => C a where
  funC :: a


