
import ClassExportImport (C (funC1, funC3))

test :: C a => a -> Bool
test x = funC3 (funC1 x)
