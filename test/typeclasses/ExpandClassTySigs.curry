

import qualified Prelude as P
import ExpandClassTySigsTypes as T

class A a where
  funA :: a -> P.String

class B a where
  funB1 :: a -> P.Char -> [T.T a]
  funB2 :: a -> [a]
  funB3 :: a -> (a, a)
  funB4 :: a -> (P.Maybe a, T.S a, U a a, T a)
  funB5 :: a -> F a [a]

