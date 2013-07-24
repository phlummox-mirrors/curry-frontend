
module TCCUse3 where

import TCC as TCC' (D, E)

class TCC a where
  funTCC :: a -> a

instance TCC Bool where

