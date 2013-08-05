
class Empty a where

instance Empty a => Empty [a] where

class Empty a => C a where
  funC :: a -> a

-- instance C a => C [a] where
--   funC x = x

instance Empty a => C [a] where
  funC x = x

test :: Empty a => a -> [[a]]
test x = funC [[x]]

test2 :: Empty a => a -> [[[a]]]
test2 x = funC [[[x]]]

test3 :: Empty a => a -> [[[[a]]]]
test3 x = funC [[[[x]]]]

instance Empty Bool where

test4 = funC [[True]]

test5 = funC [[[True]]]