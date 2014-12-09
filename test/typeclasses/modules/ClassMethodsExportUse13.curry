
import ClassMethodsExport (F(funF1))
import ClassMethodsExport hiding (F(..))

test :: F a => a -> a
test x = x

test2 x = funF1 x
