
module TCCUse4 where

import qualified TCC as T (D, E)

test :: T.D a => a -> a
test x = x

instance T.E Bool where

test2 x = T.funD x



