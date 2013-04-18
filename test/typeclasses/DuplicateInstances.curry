

class A a

class B a


instance A Int

instance A Int

instance B ()
instance B ()

instance A (c, d)
instance A (a, b)

data T a = T a

instance A (T a)
instance A (T b)
