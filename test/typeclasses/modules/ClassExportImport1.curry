
import ClassExportImport

test1 :: C a => a -> a
test1 x = x

test2 :: D a => a -> a
test2 x = x

test3 :: E a => a -> a
test3 x = x

test4 :: F a => a -> a
test4 x = x

test5 :: G a => a -> a
test5 x = x

test6 :: H a => a -> a
test6 x = x

test7 :: I a => a -> a
test7 x = x

test8 :: K a => a -> a
test8 x = x

test9 x = funC3 (funC1 (funC2 x))
