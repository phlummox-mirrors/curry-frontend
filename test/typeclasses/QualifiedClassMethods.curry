
module QualifiedClassMethods where

class A a where
  funA :: a -> a -> Bool

instance A Bool where
  funA True True = True
  funA False True = True
  funA True False = True
  funA False False = False

test1 x = QualifiedClassMethods.funA x x



class B a where
  funB :: a -> a

test2 x = QualifiedClassMethods.funB x
