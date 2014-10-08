f []           _       = Nothing
f (_      : _) []      = Nothing
f ((_, _) : _) (_ : _) = Nothing

g x = case x of
  "" -> 0
  [] -> 1
  _  -> 2

h x = fcase x of
  [_]    -> 0
  (_:[]) -> 1
  _      -> 2

i x = x
i y = y

j []    = 0
j (_:_) = 0
j _     = 1

k [] = 0
k _  = 1
