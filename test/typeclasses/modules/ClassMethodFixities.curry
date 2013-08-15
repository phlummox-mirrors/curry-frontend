
module ClassMethodFixities where

class C a where
  (**) :: a -> a -> a
  (//) :: a -> a -> a

instance C Char where
  
infixl 3 **
infixr 3 //

test = 'c' ** 'd' ** 'e'

test2 = 'c' // 'd' // 'e'

