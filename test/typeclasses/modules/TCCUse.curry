
module TCCUse where

import TCC (D, E)

class TCC a where
  funTCC :: a -> a

instance TCC Bool where

