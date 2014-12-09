

class A a where
  fun1 :: a

class B a

-- error:
class A a where
  fun2 :: a

  
class C a

class D a

-- error:
class D a
class D a