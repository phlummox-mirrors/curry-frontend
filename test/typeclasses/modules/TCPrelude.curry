

module TCPrelude 
  ( Eq(..)
  , elem, notElem, lookup
  , Ord(..)
  , Show(..), print
  , Read (..)
  , Bounded (..), Enum (..)
  -- re-export data types from the original Prelude
  , Bool (..) , Char (..) , Int (..) , Float (..), String , Ordering (..)
  , Success (..), Maybe (..), Either (..), IO (..), IOError (..)
  -- re-export functions from the original Prelude
  , (.), id, const, curry, uncurry, flip, until, seq, ensureNotFree
  , ensureSpine, ($), ($!), ($!!), ($#), ($##), error, prim_error
  , failed, (&&), (||), not, otherwise, if_then_else
  , fst, snd, head, tail, null, (++), length, (!!), map, foldl, foldl1
  , foldr, foldr1, filter, zip, zip3, zipWith, zipWith3, unzip, unzip3
  , concat, concatMap, iterate, repeat, replicate, take, drop, splitAt
  , takeWhile, dropWhile, span, break, lines, unlines, words, unwords
  , reverse, and, or, any, all
  , ord, prim_ord, chr, prim_chr, (+), prim_Int_plus, (-)
  , prim_Int_minus, (*), prim_Int_times, div, prim_Int_div, mod, prim_Int_mod
  , negate, negateFloat, prim_negateFloat, (=:=), success, (&), (&>), maybe
  , either, (>>=), return, (>>), done, putChar, prim_putChar, getChar, readFile
  , prim_readFile, prim_readFileContents, writeFile, prim_writeFile, appendFile
  , prim_appendFile, putStr, putStrLn, getLine, userError, ioError, showError
  , catch, catchFail, prim_show, doSolve, sequenceIO, sequenceIO_, mapIO
  , mapIO_, (?), unknown, getAllValues, getSomeValue, try, inject, solveAll
  , solveAll2, once, best, findall, findfirst, browse, browseList, unpack
  , PEVAL, normalForm, groundNormalForm, apply, cond, letrec, (=:<=), (=:<<=)
  , ifVar, failure
  ) where

import qualified Prelude as P ((==), (<=), show, enumFrom, enumFromTo
  , enumFromThen, enumFromThenTo)
import Prelude hiding ((==), (/=), compare, (<), (<=), (>), (>=), min, max, show)

-- -------------------------------------------------------------------------
-- Eq class and related instances and functions
-- -------------------------------------------------------------------------

class Eq a where
  (==), (/=) :: a -> a -> Bool

  x == y = not $ x /= y
  x /= y = not $ x == y

instance Eq Bool where
  False == False  = True
  False == True   = False
  True  == False  = False
  True  == True   = True

instance Eq Char where
  c == c' = c P.== c'

instance Eq Int where
  i == i' = i P.== i'

instance Eq Float where
  f == f' = f P.== f'

instance Eq a => Eq [a] where
  []    == []    = True
  []    == (_:_) = False
  (_:_) == []    = False
  (x:xs) == (y:ys) = x == y && xs == ys

instance Eq () where
  () == () = True
  
instance (Eq a, Eq b) => Eq (a, b) where
  (a, b) == (a', b') = a == a' && b == b'

instance (Eq a, Eq b, Eq c) => Eq (a, b, c) where
  (a, b, c) == (a', b', c') = a == a' && b == b' && c == c'

instance (Eq a, Eq b, Eq c, Eq d) => Eq (a, b, c, d) where
  (a, b, c, d) == (a', b', c', d') = a == a' && b == b' && c == c' && d == d'

instance (Eq a, Eq b, Eq c, Eq d, Eq e) => Eq (a, b, c, d, e) where
  (a, b, c, d, e) == (a', b', c', d', e') = a == a' && b == b' && c == c' && d == d' && e == e'

instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => Eq (a, b, c, d, e, f) where
  (a, b, c, d, e, f) == (a', b', c', d', e', f') = a == a' && b == b' && c == c' && d == d' && e == e' && f == f'

instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g) => Eq (a, b, c, d, e, f, g) where
  (a, b, c, d, e, f, g) == (a', b', c', d', e', f', g') = a == a' && b == b' && c == c' && d == d' && e == e' && f == f' && g == g'

instance Eq a => Eq (Maybe a) where
  Nothing == Nothing = True
  Just _  == Nothing = False
  Nothing == Just _  = False
  Just x  == Just y  = x == y

-- TODO: use deriving instead
instance Eq Ordering where
  LT == LT = True
  LT == EQ = False
  LT == GT = False
  EQ == LT = False
  EQ == EQ = True
  EQ == GT = False
  GT == LT = False
  GT == EQ = False
  GT == GT = True

instance Eq Success where
  Success == Success = True

instance (Eq a, Eq b) => Eq (Either a b) where
  Left x  == Left y  = x == y
  Left _  == Right _ = False
  Right _ == Left _  = False
  Right x == Right y = x == y
  
--- Element of a list?
elem :: Eq a => a -> [a] -> Bool
elem x = any (x ==)

--- Not element of a list?
notElem :: Eq a => a -> [a] -> Bool
notElem x = all (x /=)

--- Looks up a key in an association list.
lookup :: Eq a => a -> [(a, b)] -> Maybe b
lookup _ []       = Nothing
lookup k ((x,y):xys)
      | k==x      = Just y
      | otherwise = lookup k xys

-- -------------------------------------------------------------------------
-- Ord class and related instances and functions
-- -------------------------------------------------------------------------

--- minimal complete definition: compare or <=
class Eq a => Ord a where
  compare :: a -> a -> Ordering
  (<=) :: a -> a -> Bool
  (>=) :: a -> a -> Bool
  (<)  :: a -> a -> Bool
  (>)  :: a -> a -> Bool

  min :: a -> a -> a
  max :: a -> a -> a

  x < y = x <= y && x /= y
  x > y = not (x <= y)
  x >= y = y <= x
  x <= y = compare x y == EQ || compare x y == LT

  compare x y | x == y = EQ
              | x <= y = LT
              | otherwise = GT

  min x y | x <= y    = x
          | otherwise = y

  max x y | x >= y    = x
          | otherwise = y

instance Ord Bool where
  False <= False = True
  False <= True  = True
  True  <= False = False
  True  <= True  = True

instance Ord Char where
  c1 <= c2 = c1 P.<= c2

instance Ord Int where
  i1 <= i2 = i1 P.<= i2

instance Ord Float where
  f1 <= f2 = f1 P.<= f2

instance Ord Success where
  Success <= Success = True

-- TODO: use deriving instead
instance Ord Ordering where
  LT <= LT = True
  LT <= EQ = True
  LT <= GT = True
  EQ <= LT = False
  EQ <= EQ = True
  EQ <= GT = True
  GT <= LT = False
  GT <= EQ = False
  GT <= GT = True

instance Ord a => Ord (Maybe a) where
  Nothing <= Nothing = True
  Nothing <= Just _  = True
  Just _  <= Nothing = False
  Just x  <= Just y  = x <= y

instance (Ord a, Ord b) => Ord (Either a b) where
  Left x  <= Left y  = x <= y
  Left _  <= Right _ = True
  Right _ <= Left _  = False
  Right x <= Right y = x <= y

instance Ord a => Ord [a] where
  []    <= []    = True
  (_:_) <= []    = False
  []    <= (_:_) = True
  (x:xs) <= (y:ys) | x == y    = xs <= ys
                   | otherwise = x < y

instance Ord () where
  () <= () = True

instance (Ord a, Ord b) => Ord (a, b) where
  (a, b) <= (a', b') = a < a' || (a == a' && b <= b')

instance (Ord a, Ord b, Ord c) => Ord (a, b, c) where
  (a, b, c) <= (a', b', c') = a < a'
     || (a == a' && b < b')
     || (a == a' && b == b' && c <= c')

instance (Ord a, Ord b, Ord c, Ord d) => Ord (a, b, c, d) where
  (a, b, c, d) <= (a', b', c', d') = a < a'
     || (a == a' && b < b')
     || (a == a' && b == b' && c < c')
     || (a == a' && b == b' && c == c' && d <= d')

instance (Ord a, Ord b, Ord c, Ord d, Ord e) => Ord (a, b, c, d, e) where
  (a, b, c, d, e) <= (a', b', c', d', e') = a < a'
     || (a == a' && b < b')
     || (a == a' && b == b' && c < c')
     || (a == a' && b == b' && c == c' && d < d')
     || (a == a' && b == b' && c == c' && d == d' && e <= e')

-- -------------------------------------------------------------------------
-- Show class and related instances and functions
-- -------------------------------------------------------------------------

type ShowS = String -> String

class Show a where
  show :: a -> String

  showsPrec :: Int -> a -> ShowS

  showList :: [a] -> ShowS

  showsPrec _ x s = show x ++ s
  show x = shows x ""
  showList ls s = showList' shows ls s

shows :: Show a => a -> ShowS
shows = showsPrec 0

showChar :: Char -> ShowS
showChar c s = c:s

showString :: String -> ShowS
showString str s = foldr showChar s str

showParen :: Bool -> ShowS -> ShowS
showParen b s = if b then showChar '(' . s . showChar ')' else s

showList' :: (a -> ShowS) ->  [a] -> ShowS
showList' _     []     s = "[]" ++ s
showList' showx (x:xs) s = '[' : showx x (showl xs)
  where
    showl []     = ']' : s
    showl (y:ys) = ',' : showx y (showl ys)


print :: Show a => a -> IO ()
print t = putStrLn (show t)

-- -------------------------------------------------------------------------

instance Show () where
  showsPrec _ () = showString "()"

instance (Show a, Show b) => Show (a, b) where
  showsPrec _ (a, b) = showTuple [shows a, shows b]

instance (Show a, Show b, Show c) => Show (a, b, c) where
  showsPrec _ (a, b, c) = showTuple [shows a, shows b, shows c]

instance (Show a, Show b, Show c, Show d) => Show (a, b, c, d) where
  showsPrec _ (a, b, c, d) = showTuple [shows a, shows b, shows c, shows d]

instance (Show a, Show b, Show c, Show d, Show e) => Show (a, b, c, d, e) where
  showsPrec _ (a, b, c, d, e) = showTuple [shows a, shows b, shows c, shows d, shows e]

instance Show a => Show [a] where
  showsPrec _ = showList

instance Show Bool where
  showsPrec _ True = showString "True"
  showsPrec _ False = showString "False"

instance Show Ordering where
  showsPrec _ LT = showString "LT"
  showsPrec _ EQ = showString "EQ"
  showsPrec _ GT = showString "GT"


instance Show Char where
  -- TODO: own implementation instead of passing to original Prelude functions?
  showsPrec _ c = showString (P.show c)

  showList cs = showString (P.show cs)

instance Show Int where
  showsPrec _ i = showString $ P.show i

instance Show Float where
  showsPrec _ f = showString $ P.show f

instance Show a => Show (Maybe a) where
  showsPrec _ Nothing = showString "Nothing"
  showsPrec p (Just x) = showParen (p > appPrec)
    (showString "Just " . showsPrec appPrec1 x)


instance (Show a, Show b) => Show (Either a b) where
  showsPrec p (Left x) = showParen (p > appPrec)
    (showString "Left " . showsPrec appPrec1 x)
  showsPrec p (Right y) = showParen (p > appPrec)
    (showString "Right " . showsPrec appPrec1 y)
  
showTuple :: [ShowS] -> ShowS
showTuple ss = showChar '('
             . foldr1 (\s r -> s . showChar ',' . r) ss
             . showChar ')'

appPrec = 10
appPrec1 = 11

instance Show Success where
  showsPrec _ Success = showString "Success"

-- -------------------------------------------------------------------------
-- Read class and related instances and functions
-- -------------------------------------------------------------------------

class Read a where
  read :: String -> a

-- -------------------------------------------------------------------------
-- Bounded and Enum classes and instances
-- -------------------------------------------------------------------------

class Bounded a where
  minBound, maxBound :: a

class Enum a where
  succ :: a -> a
  pred :: a -> a
  
  toEnum   :: Int -> a
  fromEnum :: a -> Int
  
  enumFrom       :: a -> [a]
  enumFromThen   :: a -> a -> [a]
  enumFromTo     :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]

  succ = toEnum . (+ 1) . fromEnum
  pred = toEnum . (\x -> x -1) . fromEnum
  enumFrom x = map toEnum [fromEnum x ..]
  enumFromThen x y = map toEnum [fromEnum x, fromEnum y ..]
  enumFromTo x y = map toEnum [fromEnum x .. fromEnum y]
  enumFromThenTo x1 x2 y = map toEnum [fromEnum x1, fromEnum x2 .. fromEnum y]

instance Bounded () where
  minBound = ()
  maxBound = ()
  
instance Enum () where
  succ _      = error "TCPrelude.Enum.().succ: bad argument"
  pred _      = error "TCPrelude.Enum.().pred: bad argument"

  toEnum x | x == 0    = ()
           | otherwise = error "TCPrelude.Enum.().toEnum: bad argument"

  fromEnum () = 0
  enumFrom ()         = [()]
  enumFromThen () ()  = let many = ():many in many
  enumFromTo () ()    = [()]
  enumFromThenTo () () () = let many = ():many in many

instance Bounded Bool where
  minBound = False
  maxBound = True
  
instance Enum Bool where
  succ False = True
  succ True  = error "TCPrelude.Enum.Bool.succ: bad argument"

  pred False = error "TCPrelude.Enum.Bool.pred: bad argument"
  pred True  = False

  toEnum n | n == 0 = False
           | n == 1 = True
           | otherwise = error "TCPrelude.Enum.Bool.toEnum: bad argument"

  fromEnum False = 0
  fromEnum True  = 1


instance (Bounded a, Bounded b) => Bounded (a, b) where
  minBound = (minBound, minBound)
  maxBound = (maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c) => Bounded (a, b, c) where
  minBound = (minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c, Bounded d) => Bounded (a, b, c, d) where
  minBound = (minBound, minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound, maxBound)

instance (Bounded a, Bounded b, Bounded c, Bounded d, Bounded e) => Bounded (a, b, c, d, e) where
  minBound = (minBound, minBound, minBound, minBound, minBound)
  maxBound = (maxBound, maxBound, maxBound, maxBound, maxBound)



instance Bounded Ordering where
  minBound = LT
  maxBound = GT

instance Enum Ordering where
  succ LT = EQ
  succ EQ = GT
  succ GT = error "TCPrelude.Enum.Ordering.succ: bad argument"

  pred LT = error "TCPrelude.Enum.Ordering.pred: bad argument"
  pred EQ = LT
  pred GT = EQ

  toEnum n | n == 0 = LT
           | n == 1 = EQ
           | n == 2 = GT
           | otherwise = error "TCPrelude.Enum.Ordering.toEnum: bad argument"

  fromEnum LT = 0
  fromEnum EQ = 1
  fromEnum GT = 2

-- TODO:
-- instance Enum Char
-- instance Bounded Char where

-- TODO: 
-- instance Enum Float where

-- TODO (?):
-- instance Bounded Int where

instance Enum Int where
  -- TODO: is Int unbounded?
  succ x = x + 1
  pred x = x - 1

  -- TODO: correct semantic?
  toEnum n = n
  fromEnum n = n

  -- TODO: provide own implementations?
  enumFrom = P.enumFrom
  enumFromTo = P.enumFromTo
  enumFromThen = P.enumFromThen
  enumFromThenTo = P.enumFromThenTo

{-
boundedEnumFrom :: (Enum a, Bounded a) => a -> [a]
boundedEnumFrom n = map toEnum [fromEnum n .. fromEnum (maxBound `asTypeOf` n)]

boundedEnumFromThen :: (Enum a, Bounded a) => a -> a -> [a]
boundedEnumFromThen n1 n2
  | i_n2 >= i_n1  = map toEnum [i_n1, i_n2 .. fromEnum (maxBound `asTypeOf` n1)]
  | otherwise     = map toEnum [i_n1, i_n2 .. fromEnum (minBound `asTypeOf` n1)]
  where
    i_n1 = fromEnum n1
    i_n2 = fromEnum n2
-}