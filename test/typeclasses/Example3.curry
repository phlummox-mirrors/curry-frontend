
class Eq a where
  eq :: a -> a -> Bool

instance (Eq a, Eq b) => Eq (a, b) where
  eq (x1, y1) (x2, y2) = eq x1 x2 && eq y1 y2

type Dict_Eq a = (a -> a -> Bool, a -> a -> Bool)




def_neq :: Eq a => a -> a -> Bool

def_neq x y = error ""

impl_eq :: (Eq a, Eq b) => (a, b) -> (a, b) -> Bool

impl_eq = error ""

dict :: (Eq a, Eq b) => Dict_Eq (a, b)

dict = (impl_eq, def_neq)
