
module Traversal where


type Traversable a b = a -> ([b], [b] -> a)

children :: Traversable a b -> a -> [b]
children tr = fst . tr

type FunList a = [a] -> [a]

concatFL :: [FunList a] -> FunList a
concatFL [] ys = ys
concatFL (x:xs) ys = x (concatFL xs ys)

familyFL :: Traversable a a -> a -> FunList a
familyFL tr x xs = x : childFamiliesFL tr tr x xs

childFamiliesFL :: Traversable a b -> Traversable b b -> a -> FunList b
childFamiliesFL tra trb x xs = concatFL (map (familyFL trb) (children tra x)) xs



