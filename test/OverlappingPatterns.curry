f []           _            = Nothing
f (_      : _) []           = Nothing
f ((_, _) : _) ((_, _) : _) = Nothing

g x = fcase x of
  "" -> 0
  [] -> 1

g x = fcase x of
  [_]    -> 0
  (_:[]) -> 1
  _      -> 2

i x = x
i y = y

j []    = 0
j (_:_) = 0
j x     = 1
