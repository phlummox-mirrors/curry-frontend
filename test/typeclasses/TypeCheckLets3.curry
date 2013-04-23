
{-
class B b where
  b :: b -> b -> True

-- b _ _ = True


f y = let a x = b x y in a 2
f y = let a x = b x y; y = 10 in a 2
f y = let a x = b x y where y = 2  in a 2
f y = let a x = b x y where z = 1 where y = 2  in a 2
f y = let a x = b x y where z = let y = 2 in 1 in a 2

 -}


class B b where
  b :: b -> b -> Bool

-- b _ _ = True

instance B Char where

f1 y = let a x = b x y in a 'c'
f2 y = let a x = b x y; y = 'c' in a 'c'
f3 y = let a x = b x y where y = 'c'  in a 'c'
f4 y = let a x = b x y where z = 'c' where y = 'd'  in a 'e'
f5 y = let a x = b x y where z = let y = 'd' in 'a' in a 'f'

