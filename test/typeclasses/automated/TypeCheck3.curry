
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

fun3b :: D a => a -> b -> Bool
fun3b = error ""

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

class G a where
  fun6 :: a -> a -> a -> Bool

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


testLS1 x y = (fun x &&) (fun4 y)

testLS1b x y = (fun x &&) (fun3 y y)

testLS1c x y = (fun3 x x &&) (fun y)

testLS2 x y = (fun4 x &&) (fun y)

testLS3 x y = (fun x `fun3`) (fun4 y)

-- testLS3b x y z = (fun2 x `fun3 z`) (fun4 y)

testLS4 x y = (fun4 x `fun3`) (fun4 y)
testLS4b x y = (fun4 x `fun3b`) (fun4 y)

testLS5 x y = (fun4 x `fun3`) (fun4 'c')

testLS6 x y = (fun4 'c' `fun3`) (fun4 x)

testLS7 x = (fun4 'c' `fun3`) (fun4 x)



testRS1 x y = (&& fun x) (fun4 y)

testRS1b x y = (&& fun x) (fun3 y y)

testRS2 x y = (&& fun4 x) (fun y)

testRS3 x y = (`fun3` fun x) (fun4 y)
testRS3b x y = (`fun3` fun2 x) (fun4 y)

testRS4 x y = (`fun3` fun4 x) (fun4 y)
testRS4b x y = fun3 (fun4 x) (fun4 y)

testRS5 x y = (`fun3` fun4 x) (fun4 'c')

testRS6 x y = (`fun3` fun4 'c') (fun4 x)

