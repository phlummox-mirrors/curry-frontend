
module ExpandClassTySigsTypes where

data T a = T a

data S a = S a

data U a b = U a b

type F a b = U b a

