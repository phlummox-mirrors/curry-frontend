
import ClassMethodsExport (J(..))

import ClassMethodsExport hiding (I(funI1))


test :: J a => a -> a
test x = x

test2 x = funI2 (funI3 x)

