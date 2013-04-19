
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

test0 x = fun x

test1 x = fun2 x
test1 x = fun4 x

test2 x = fun x
test2 x = fun3 x x

test3 x = fun2 x
test3 x = fun4 x
test3 x = fun5 x

test4 x = fun2 x
test4 x = fun4 x
test4 x = x

test5 x = fun x
test5 x = fun x && fun x


testLS x y = (fun x &&) (fun4 y)

testLS2 x y = (fun4 x &&) (fun y)

testLS3 x y = (fun x `fun3`) (fun4 y)

testLS4 x y = (fun4 x `fun3`) (fun4 y)

testLS5 x y = (fun4 x `fun3`) (fun4 'c')

testLS6 x y = (fun4 'c' `fun3`) (fun4 x)

testLS7 x = (fun4 'c' `fun3`) (fun4 x)



testRS x y = (&& fun x) (fun4 y)

testRS2 x y = (&& fun4 x) (fun y)

testRS3 x y = (`fun3` fun x) (fun4 y)

testRS4 x y = (`fun3` fun4 x) (fun4 y)
testRS4b x y = fun3 (fun4 x) (fun4 y)

testRS5 x y = (`fun3` fun4 x) (fun4 'c')

testRS6 x y = (`fun3` fun4 'c') (fun4 x)

