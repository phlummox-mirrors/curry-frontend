f = case 0 ? 1 of
      0 -> 0
      1 -> 1
      v -> v

g = case [1..10] of
  []       -> 0
  (1:xs)   -> 1 + length xs
  (1:2:xs) -> 2 + length xs
  _        -> 10

h []       = 0
h (1:xs)   = 1 + length xs
h (1:2:xs) = 2 + length xs
