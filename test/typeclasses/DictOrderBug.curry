
class Eq a where
  eq :: a -> a -> Bool
  neq :: a -> a -> Bool

  neq x y = not $ eq x y


instance (Eq a, Eq b) => Eq (a, b) where
  eq (x1, y1) (x2, y2) = eq x1 x2 && eq y1 y2
  -- neq (x1, y1) (x2, y2) = neq x1 x2 || neq y1 y2

test1 :: (Eq a, Eq b) => (a, b) -> (a, b) -> Bool
test1 (x, y) (x2, y2) = eq (x, y) (x2, y2)


instance (Eq a, Eq b, Eq c) => Eq (a, b, c) where
  eq (x1, y1, z1) (x2, y2, z2) = eq x1 x2 && eq y1 y2

test2 :: (Eq a, Eq b, Eq c) => (a, b, c) -> (a, b, c) -> Bool
test2 (x, y, z) (x2, y2, z2) = eq (x, y, z) (x2, y2, z2)


instance (Eq a, Eq b, Eq c, Eq d) => Eq (a, b, c, d) where
  eq (x1, y1, z1, u1) (x2, y2, z2, u2) = eq x1 x2 && eq y1 y2

test3 :: (Eq a, Eq b, Eq c, Eq d) => (a, b, c, d) -> (a, b, c, d) -> Bool
test3 (x, y, z, u) (x2, y2, z2, u2) = eq (x, y, z, u) (x2, y2, z2, u2)

instance (Eq a, Eq b, Eq c, Eq d, Eq e) => Eq (a, b, c, d, e) where
  eq (x1, y1, z1, u1, v1) (x2, y2, z2, u2, v2) = eq x1 x2 && eq y1 y2

test4 :: (Eq a, Eq b, Eq c, Eq d, Eq e) => (a, b, c, d, e) -> (a, b, c, d, e) -> Bool
test4 (x, y, z, u, v) (x2, y2, z2, u2, v2) = eq (x, y, z, u, v) (x2, y2, z2, u2, v2)

