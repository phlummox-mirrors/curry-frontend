

(===) :: a -> a -> Bool
(===) x y = True

fun :: a -> b -> a
fun x y = x

-- infix apply

test1 x y = x === y

test2 x y = x `fun` y

test3 = True === False

test4 = True `fun` 'a'


-- left sections

test5 x y = (x ===) y

test6 x y = (x `fun`) y

test7 = (True ===) False

test8 = (True `fun`) 'a'


-- right sections

test9 x y = (=== y) x

test10 x y = (`fun` y) x

test11 = (=== False) True

test12 = (`fun` 'a') True

