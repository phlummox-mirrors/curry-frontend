

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

test3 x = let y3 = fun2 x in x

test4 x = let Just y4 = Just $ fun2 x in x

test5 x = let y5a :>: y5b = fun2 x :>: fun4 x in x

test6 x = let (y6) = fun2 x in x

-- test6b x = let () = fun2 x in x

test7 x = let (y7a, y7b) = (fun2 x, fun4 x) in x


test8a x = let [y8a1, y8a2, y8a3] = [fun2 x, fun4 x, fun5 x] in x

test8b x = let [] = [] in x

test8c x = let [y8c] = [fun2 x] in x

test8d x = let [y8a1, y8a2, y8a3] = [True, False, True] in x

test9 x = let y9@(y9a, y9b) = (fun2 x, fun4 x) in x

test10 x = let ~[y10] = [fun2 x] in x



-- test11 x = let Just (x1, [Left x2, Right x3], x4@(x5, x6, x7)) = Just (fun2 x, [Left $ fun4 x, Right $ fun5 x], (fun x, fun2 x, 1)) in x

test12 x = let Just (x1, x2) = Just (fun2 x, fun4 x) in x

-- test13 x = let Just (x1, [Left x2, Right x3]) = Just (fun2 x, [Left $ fun4 x, Right $ fun4 x]) in x

test14 x = let Just (x1, x4@(Left x2, x3)) = Just (fun2 x, (Left $ fun4 x, fun5 x)) in x

















