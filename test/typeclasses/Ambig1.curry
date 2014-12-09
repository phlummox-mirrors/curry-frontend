

class Text a where
  put :: a -> String
  get :: String -> [(a, String)]

putget d s = put a where (a, s') = head (get s)

