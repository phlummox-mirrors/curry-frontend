
class C a where

class C1 a where

class C2 a where

class C3 a where


data (C1 a, C2 b, C3 c) => T a b c = T1 a | T2 b | T3 c | T4 a c | T5 a b c

newtype (C1 a, C2 b, C3 c) => T2 a b c = T' c

