

class Text a where
  put :: a -> String -> String
  get :: String -> [(a, String)]
  read :: String -> a

instance Text Int where
  
add n s = s ++ " + " ++ show n ++ " is " ++ showaddn
  where showaddn = put (read s + n) ""
  -- where showaddn = put (read s)
  -- where showaddn = put (read s && n)

-- showaddn = put (read "")