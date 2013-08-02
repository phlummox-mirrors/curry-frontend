

module TCPrelude 
  ( Eq(..)
  , Bool (..)
  ) where

import qualified Prelude as P ((==))
import Prelude hiding ((==))

class Eq a where
  (==), (/=) :: a -> a -> Bool

  x == y = not $ x /= y
  x /= y = not $ x == y

instance Eq Bool where
  False == False  = True
  False == True   = False
  True  == False  = False
  True  == True   = True

instance Eq Char where
  c == c' = c P.== c'

instance Eq Int where
  i == i' = i P.== i'

instance Eq Float where
  f == f' = f P.== f'

instance Eq a => Eq [a] where
  []    == []    = True
  []    == (_:_) = False
  (_:_) == []    = False
  (x:xs) == (y:ys) = x == y && xs == ys

instance (Eq a, Eq b) => Eq (a, b) where
  (a, b) == (a', b') = a == a' && b == b'

instance (Eq a, Eq b, Eq c) => Eq (a, b, c) where
  (a, b, c) == (a', b', c') = a == a' && b == b' && c == c'

instance (Eq a, Eq b, Eq c, Eq d) => Eq (a, b, c, d) where
  (a, b, c, d) == (a', b', c', d') = a == a' && b == b' && c == c' && d == d'

instance (Eq a, Eq b, Eq c, Eq d, Eq e) => Eq (a, b, c, d, e) where
  (a, b, c, d, e) == (a', b', c', d', e') = a == a' && b == b' && c == c' && d == d' && e == e'

instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => Eq (a, b, c, d, e, f) where
  (a, b, c, d, e, f) == (a', b', c', d', e', f') = a == a' && b == b' && c == c' && d == d' && e == e' && f == f'

instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g) => Eq (a, b, c, d, e, f, g) where
  (a, b, c, d, e, f, g) == (a', b', c', d', e', f', g') = a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g'

