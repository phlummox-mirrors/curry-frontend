

import ClassMethodsExport (F(..))

test :: F a => a -> a
test x = x

test2 x = funF3 (funF1 (funF2 x)) x

