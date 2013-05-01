

class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a

class G a where
  fun6 :: a -> Bool

class H a where
  fun7 :: a -> a -> Bool


data T a b = a :>: b

-- Test all possible pattern types!

test1 x = let 1 = fun2 x in x

test2 x = let -1 = fun2 x in x

test3 x = let y3 = fun2 x in y3

test4 x = let Just y4 = Just $ fun2 x in y4

test5a x = let y5a :>: y5b = fun2 x :>: fun4 x in x
test5b x = let y5a :>: y5b = fun2 x :>: fun4 x in y5a
test5c x = let y5a :>: y5b = fun2 x :>: fun4 x in y5b
test5d x = let y5a :>: y5b = fun2 x :>: fun4 x in (y5a, y5b)

test6 x = let (y6) = fun2 x in y6

test6b x = let () = fun2 x in x

test7 x = let (y7a, y7b) = (fun2 x, fun4 x) in y7a


test8a x = let [y8a1, y8a2, y8a3] = [fun2 x, fun4 x, fun5 x] in y8a1

test8b x = let [] = [] in x

test8c x = let [y8c] = [fun2 x] in y8c

test8d x = let [y8a1, y8a2, y8a3] = [True, False, True] in y8a1

test9a x = let y9@(y9a, y9b) = (fun2 x, fun4 x) in y9
test9b x = let y9@(y9a, y9b) = (fun2 x, fun4 x) in y9a

test10 x = let ~[y10] = [fun2 x] in y10


-- combinations

test11 x = let Just (x1, [Left x2, Right x3], x4@(x5, x6, x7)) = Just (fun2 x, [Left $ fun4 x, Right $ fun5 x], (fun x, fun2 x, 1)) in x1

test11b x = let y = Just (fun2 x, [Left $ fun4 x, Right $ fun5 x], (fun x, fun2 x, 1)) in y

test12 x = let Just (x1, x2) = Just (fun2 x, fun4 x) in x1

test13 x = let Just (x1, [Left x2, Right x3]) = Just (fun2 x, [Left $ fun4 x, Right $ fun4 x]) in x1

test14 x = let Just (x1, x4@(Left x2, x3)) = Just (fun2 x, (Left $ fun4 x, fun5 x)) in x2


test15 x = let  [Left x2, Right x3] =  [Left $ fun4 x, Right $ fun5 x] in x2

test15b x y = let  [Left x2, Right x3] =  [Left $ fun4 x, Right $ fun5 y] in (x2, x3)

test15c x y = let x2 = fun4 x; x3 = fun5 y in (x2, x3)

test16 x = let  [Left x2] =  [Left $ fun4 x] in x2

test17 x = [Left $ fun4 x, Right $ fun5 x]



test18 x = let x2 = fun4 x in x2

test19 x = let y = fun2 y in y

test20 x = x1
  where Just (x1, [Left x2, Right x3], x4@(x5, x6, x7)) = Just (fun2 x, [Left $ fun4 x, Right $ fun5 x], (fun x, fun2 x, 1))


