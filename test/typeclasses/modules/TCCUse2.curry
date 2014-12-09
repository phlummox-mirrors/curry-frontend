
module TCCUse2 where

import qualified TCC as T (D, E)

class TCC a where
  funTCC :: a -> a

instance TCC Bool where

