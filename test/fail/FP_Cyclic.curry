{-# Language FunctionalPatterns #-}

f  = let f3 (g _) = 0
      in 42
g x = let f1 = f in x
