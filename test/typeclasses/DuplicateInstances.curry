

class A a

class B a


instance A Int

instance A Int

instance B ()
instance B ()

instance A (c, d)
instance A (a, b)

instance A (a, b, c)
instance A (d, e, f)

data T a = T a

instance A (T a)
instance A (T b)

data S a b = S a b

instance A (S a b)
instance A (S a c)

instance A [a]
instance A [b]

instance B (a -> b)
instance B (c -> d)


