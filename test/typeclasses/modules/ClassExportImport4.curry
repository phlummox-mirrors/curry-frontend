
import ClassExportImport (C (..))

test :: C a => a -> a
test x = x

test2 x = funC3 (funC1 (funC2 x))
