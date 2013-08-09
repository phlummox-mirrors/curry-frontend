
import ClassMethodsExport (F(funF1))
import ClassMethodsExport (F(funF3))

test :: F a => a -> a
test x = funF2 x
