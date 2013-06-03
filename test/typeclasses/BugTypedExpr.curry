
class A a where

class A a => B a where

class B a => C a where



test1 x = (test2 :: a -> a) x

test2 x = (test1 :: a -> a) x


-- internalError!
test3 x = (test3 :: (C a, B a, A a) => a -> a) x

-- internalError!
test4 x = (test5 :: (C a, B a, A a) => a -> a) x

test5 x = test4 x

-- message of haskell:

{-
BugTypedExpr2.hs:16:12:
    Could not deduce (a ~ a1)
    from the context (A a, C a, B a)
      bound by the inferred type of test3 :: (A a, C a, B a) => a -> a
      at BugTypedExpr2.hs:16:1-48
    or from (C a1, B a1, A a1)
      bound by an expression type signature:
                 (C a1, B a1, A a1) => a1 -> a1
      at BugTypedExpr2.hs:16:12-45
      `a' is a rigid type variable bound by
          the inferred type of test3 :: (A a, C a, B a) => a -> a
          at BugTypedExpr2.hs:16:1
      `a1' is a rigid type variable bound by
           an expression type signature: (C a1, B a1, A a1) => a1 -> a1
           at BugTypedExpr2.hs:16:12
    Expected type: a1 -> a1
      Actual type: a -> a
    In the expression: test3 :: (C a, B a, A a) => a -> a
    In the expression: (test3 :: (C a, B a, A a) => a -> a) x
      -}

test6 = test6 :: (C a, B a, A a) => a

test7 x = (test8 :: (C a, B a, A a) => a -> a) x

test7b x = (id :: (C a, B a, A a) => a -> a) x


test8 :: B a => a -> a
test8 x = x
