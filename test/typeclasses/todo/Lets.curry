class B b where
  b :: b -> b -> Bool


instance B Char where

-- TODO: what to do with constrained variables like integers?

f6 y = let a x = b x y in a 2
f7 y = let a x = b x y; y = 10 in a 2
f8 y = let a x = b x y where y = 2  in a 2
f9 y = let a x = b x y where z = 1 where y = 2  in a 2
f10 y = let a x = b x y where z = let y = 2 in 1 in a 2