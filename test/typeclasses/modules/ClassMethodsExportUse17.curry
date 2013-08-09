
import ClassMethodsExport hiding (F(funF1, funF2, funF3))
import ClassMethodsExport (F(funF3))

test :: F a => a -> Bool
test x = funF3 x x
