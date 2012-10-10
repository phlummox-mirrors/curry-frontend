-- f using flex case
ff zs = fcase zs of
  (x:_)    -> x
  (_:y:_)  -> y

-- f using rigid case
fr zs = case zs of
  (x:_)    -> x
  (_:y:_)  -> y

-- f using patterns (should equal flex case)
fp (x:_)   = x
fp (_:y:_) = y

-- g using flex case
gf zs = fcase zs of
  (x:_)   | x > 0 -> x
  (_:y:_) | y > 0 -> y

-- g using rigid case
gr zs = case zs of
  (x:_)   | x > 0 -> x
  (_:y:_) | y > 0 -> y

-- g using patterns (should equal flex case)
gp (x:_)   | x > 0 = x
gp (_:y:_) | y > 0 = y
