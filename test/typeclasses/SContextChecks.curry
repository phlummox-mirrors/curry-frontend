
class C1 a

class C2 a

class (C1 a, C2 a) => C3 a

-- error!
-- class (C4 a, C2 a) => C3 a

class C5 a

class C5 a => C6 a

instance C3 T

instance C1 a => C2 T

instance (C1 a, C2 a) => C2 (T a)

-- error!
-- instance (Cx a, C2 a) => C2 (T a)