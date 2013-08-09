
import ClassMethodsExport (J(..), I(..))

import ClassMethodsExport hiding (I(..))

test :: I a => a -> a
test x = funI1 (funI2 (funI3 x))



