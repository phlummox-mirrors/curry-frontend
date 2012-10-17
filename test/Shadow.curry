module Shadow where

main = do
  x <- return True
  x <- return False
  return x

main2 = do
  let x = True
  let x = False
  return x

f x = g 1 where g x = x

lc = [x | x <- [1..10], x <- [1..10]]