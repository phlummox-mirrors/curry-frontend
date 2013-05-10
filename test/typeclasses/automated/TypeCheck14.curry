

class A a where
  (&&&) :: a -> a -> a
  (|||) :: a -> b -> a
  (///) :: b -> a -> a

class B a where
  funB :: a -> a

class C a where
  funC :: a -> a

test1 x y = (funB x) &&& (funC y)

test2 x y = (funB x &&&) (funC y)

test3 x y = (&&& funB x) (funC y)


test4 x y = (1::Int) ||| True

test5 x y = ((1::Int) |||) True

test6 x y = (||| (1::Int)) True


test7 x y = (1::Int) /// True

test8 x y = ((1::Int) ///) True

test9 x y = (/// (1::Int)) True


test10 x y = (1::Int) ||| (funB y)

test11 x y = ((1::Int) |||) (funB y)

test12 x y = (||| (1::Int)) (funB y)


test13 x y = (1::Int) /// (funB y)

test14 x y = ((1::Int) ///) (funB y)

test15 x y = (/// (1::Int)) (funB y)
