
module ClassEnv where

class C a where
  funA :: a -> a

test1 :: C a => a -> a
test1 x = funA x

test2 :: ClassEnv.C a => a -> a
test2 x = funA x

class C a => D a where


class ClassEnv.C a => E a where

instance C Bool where
  funA x = x
instance C Int where
