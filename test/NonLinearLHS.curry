
multi x y y x = x + y

nested (x:x:_) x = x

funpat (n + n) = n

combined ~(v:_) v = v
