

class A a where
  funA :: a -> a


-- ($) :: a -> b -> c -> a
(x $ y) z = funA x

-- ($$) :: a -> b -> c -> a
-- (x $$ y) z = funA x

-- (==) :: a -> b -> c -> a
-- (x == y) z = funA x


-- (==) :: a -> b -> a
x == y = funA x


-- id :: a -> a
-- id x = funA x
id x y z = funA x


-- id2 x = funA x

