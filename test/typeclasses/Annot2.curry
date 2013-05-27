
class A a where
  funA :: a -> a

instance A Int where
  funA x = x

instance A a => A [a] where
  funA xs = map funA xs

