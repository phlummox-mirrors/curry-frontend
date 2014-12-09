
import ClassMethodsExport (F(funF1))
import ClassMethodsExport (F(funF3))

test :: F a => a -> Bool
test x = funF3 x (funF1 x)
