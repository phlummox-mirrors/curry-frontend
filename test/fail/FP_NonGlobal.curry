{-# Language FunctionalPatterns #-}

f = let f1 x      = x
        f2 (f1 _) = 42
     in f2

