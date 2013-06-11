

class C a where
  fun :: a -> b -> Bool

instance C Bool where
  fun _ _ = True
  
f u xs ys = fun u xs && fun u ys

test = f True [1.0] ['a']

