test x = case x of
  Just 1 -> True
  Just 2 -> True

test2 (Just True) = False

and True True = True

plus 1 1 = 2

len2 [_,_] = True

tuple (True, 1) = True

tuple2 [(_,_)] = True
