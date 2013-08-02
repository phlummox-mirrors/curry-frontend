
module AsImportBug2 where

import AsImportBug1 as Q
 
class D a where
  funD :: a -> Q.T a
  
instance D Bool where
  funD x = error ""
 
instance Q.C Bool where
  funC x = error ""
  
instance Q.C Char where
  
data S a = S a

instance Q.C (S a) where
  funC x = T x
  
instance D (S a) where
  funD x = T x
  
class E a where
  funE :: a -> Q.T a
  
  funE x = Q.T x
  
class F a where
  funF :: a -> S a
  funF x = S x

instance F (Q.T a) where
  funF x = S x
  
instance F (S a) where
  funF x = S x

instance Q.C a => F (Maybe a) where
  funF x = S x
  
