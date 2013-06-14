

test = x
  where
    -- all of the following type signatures produce an internal error
    -- (Prelude.(!!): index too large)
    x :: a -> Int
    -- x :: a
    -- x :: a -> a
    x free
