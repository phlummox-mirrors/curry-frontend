
fun :: a -> Bool
fun _ = True

fun3 :: a -> a -> Bool
fun3 _ _ = False

type Rec a = { a :: a, b :: Bool }

-- When commenting the following line, the compilation works.
-- Else it doesn't work (very strange...)
testRecSel1 = { a := 'c', b := True } :> a

testRecSel2 x y = { a := fun x, b := fun3 y y } :> a
