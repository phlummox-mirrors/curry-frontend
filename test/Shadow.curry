module Shadow where

main = do
  x <- return True
  x <- return False
  return x

main2 = do
  let x = True
  let x = False
  return x