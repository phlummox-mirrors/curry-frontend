
-- file with nearly all elements of the abstract syntax tree

module AllOfAST where

-- ---------------------------------
-- Declarations
-- ---------------------------------

infixl 5 ##

data T a b = T1 a b | T2 a b

newtype NT a = T a

type List a = [a]

test1, test2 :: a -> a
test1 x = x
test2 x = x

fun x y = x

x ## y = x

(x $$$ y) z = x

test3 x = x
  where test3' = 'c'

test4 x | x == 'a' = 'a'
        | x == 'b' = 'b'
  where test4' = 'c'

-- foreign -- TODO

test5, test6 :: Int
test5, test6 external

test7 = 'a'
  where Just x = Just 'z'
        y free

-- ---------------------------------
-- Patterns
-- ---------------------------------
        
data S a b = a :<: b
        
-- TODO: NegativePattern
test8 1 x (T1 a b) (y :<: z) (T1 (T2 u u) v) ((a)) (c, d) [e] f@[g] ~h = 2

-- TODO: functional patterns

-- ---------------------------------
-- Expressions
-- ---------------------------------

test9_1 = 'a'
test9_2 x = x
test9_3 = T1 1 2
test9_4 = ('a')
test9_5 x = (x :: Char)
test9_6 x = (x, x, x)
test9_7 x = [x, x]
test9_8 x = [ x | let a = 1
                , x <- [1, 2, 3]
                , x /= 2 ]
test9_9 = [1..]
test9_10 = [1,2..]
test9_11 = [1..10]
test9_12 = [1,2..10]
test9_13 = -1
test9_14 f x = f x
test9_15 x y = x $ y
test9_16 x y = (x $) y
test9_17 x y = ($ y) x
test9_18 = \x -> x
test9_19 x = let a = 'c' in x
test9_20 x = do
  let a = 1
  y <- return [1, 2, 3]
  return y
test9_21 x = if x == 'a' then 1 else 2
test9_22 x = case x of
              'a' -> 1
              'b' -> 2

-- TODO: records
















