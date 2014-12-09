

import qualified Prelude as P

class A a where
  funA :: a -> P.String

test :: A a => a -> P.String
test x = funA x

