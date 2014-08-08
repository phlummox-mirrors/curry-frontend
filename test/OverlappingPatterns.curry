h x = fcase x of
  "" -> 0
  [] -> 1

i x = fcase x of
  [_]    -> 0
  (_:[]) -> 1
  _      -> 2

j []    = 0
j (_:_) = 0
j x     = 1

h x = x
h y = y
