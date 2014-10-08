{-# LANGUAGE FunctionalPatterns #-}

firstLastCaseFun ([x] ++ _ ++ [y]) = (x, y)

firstLastCase xs = case xs of
  ([x] ++ _ ++ [y]) -> (x, y)

firstLastLambda xs = (\([x] ++ _ ++ [y]) -> (x, y)) xs

firstLastListcomp xs = [ (x, y) | ([x] ++ _ ++ [y]) <- xs ]

firstLastDoseq xs = do
  ([x] ++ _ ++ [y]) <- return xs
  return (x, y)
