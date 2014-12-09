

class B a

class C a

class (A a, B a) => D a

class C a => E a

class (D a, E a) => F a


-- class A a
-- error:
class F a => A a

 

{-
-- error:
class B a => A a

class A a => B a
-}