
import ClassMethodsExport (F(..))
import ClassMethodsExport hiding (F(..))

test :: F a => a -> Bool
test x = funF3 x (funF1 (funF2 x))