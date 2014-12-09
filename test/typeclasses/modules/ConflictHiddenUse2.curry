
import ConflictHidden1 (D)
import ConflictHidden2 (E)

class C a where

test :: C a => a -> a
test x = x
