
class C a where

class C1 a where

class C2 a where


data T a b = T a b

data C a => S a = S a

data C a => U a b = U1 a b | U2 a b

data (C1 a, C2 a) => V a b c = V a b c

data (C1 a, C2 c) => V2 a b c = V2 a b c

data R a b c = R1 | R2 a c | R3 b

data O d c b a = O1 | O2 d b | O3 c a | O4 a b c d

newtype W a b = W a

newtype C a => X a b = X a

newtype (C1 a, C2 a) => Y a b = Y a

newtype (C1 a, C2 c) => Z c b a = Z b

