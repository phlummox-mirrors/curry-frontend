

class C a where
  fun :: a -> Bool
  fun2 :: a -> a

class D a where
  fun3 :: a -> a -> Bool

class E a where
  fun4 :: a -> a

class F a where
  fun5 :: a -> a



testLet z =
  let b = fun5 z
  in b 


testLet2 x y z =
  let a = fun3 y y
      b = fun5 z
  in fun x && a && fun b

testWhere2 x y z =
  fun x && a && fun b
  where a = fun3 y y
        b = fun5 z
  
-- b z = fun5 z


test4 x y z = [fun x && a && fun b | let a = fun3 y y
                                         b = fun5 z]


testDo12 x y z = do
  let ad = fun3 y y
      bd = fun5 z
      cd v = fun2 v
  return (fun x && ad && fun bd)
