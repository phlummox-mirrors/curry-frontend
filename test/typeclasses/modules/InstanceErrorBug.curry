
import qualified Prelude as P

class C a where
  funC :: a -> a

instance C P.Bool where
  -- no implementation
