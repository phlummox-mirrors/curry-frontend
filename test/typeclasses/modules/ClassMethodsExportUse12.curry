
import ClassMethodsExport (F(funF1))
import ClassMethodsExport hiding (F(funF3))

test :: F a => a -> a
test x = funF1 (funF2 x)
