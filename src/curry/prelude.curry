----------------------------------------------------------------------------
--- The standard prelude of Curry.
--- All top-level functions defined in this module
--- are always available in any Curry program.
----------------------------------------------------------------------------

module prelude where
-- Lines beginning with "--++" are part of the prelude
-- but cannot parsed by the compiler

-- Infix operator declarations:

infixl 9 !!
infixr 9 .
infixl 7 *, `div`, `mod`
infixl 6 +, -
-- infixr 5 :                          -- declared together with list
infixr 5 ++
infix  4 =:=, ==, /=, <, >, <=, >=
infix  4  `elem`, `notElem`
infixr 3 &&
infixr 2 ||
infixl 1 >>, >>=
infixr 0 $, $!, `seq`, &, &>, ?


-- Some standard combinators:

--- Function composition.
(.)   :: (b -> c) -> (a -> b) -> (a -> c)
f . g = \x -> f (g x)

--- Identity function.
id              :: a -> a
id x            = x

--- Constant function.
const           :: a -> _ -> a
const x _       = x

--- Converts an uncurried function to a curried function.
curry           :: ((a,b) -> c) -> a -> b -> c
curry f a b     =  f (a,b)

--- Converts an curried function to a function on pairs.
uncurry         :: (a -> b -> c) -> (a,b) -> c
uncurry f (a,b) = f a b

--- (flip f) is identical to f but with the order of arguments reversed.
flip            :: (a -> b -> c) -> b -> a -> c
flip  f x y     = f y x

--- Repeats application of a function until a predicate holds.
until          :: (a -> Bool) -> (a -> a) -> a -> a
until p f x     = if p x then x else until p f (f x)

--- Right-associative application.
($)             :: (a -> b) -> a -> b
f $ x           = f x

--- Evaluates the argument to head normal form and returns it.
--- Suspends until the result is bound to a non-variable term.
ensureNotFree :: a -> a
ensureNotFree external

--- Evaluates the argument to spine form and returns it.
--- Suspends until the result is bound to a non-variable spine.
ensureSpine :: [a] -> [a]
ensureSpine l = ensureList (ensureNotFree l)
 where ensureList []     = []
       ensureList (x:xs) = x : ensureSpine xs

--- Evaluates the first argument to head normal form (which could also
--- be a free variable) and returns the second argument.
seq     :: _ -> a -> a
seq external

--- Right-associative application with strict evaluation of its argument.
($!)    :: (a -> b) -> a -> b
f $! x  = x `seq` f x

--- Aborts the execution with an error message.
error :: String -> _
error external

--- A non-reducible polymorphic function.
--- It is useful to express a failure in a search branch of the execution.
failed :: _ 
failed | 1=:=2 = x where x free


-- Boolean values
-- already defined as builtin, since it is required for if-then-else
-- (no longer true for the MCC front-end)
data Bool = True | False

--- Sequential conjunction on Booleans.
(&&)            :: Bool -> Bool -> Bool
True  && x      = x
False && _      = False
 

--- Sequential disjunction on Booleans.
(||)            :: Bool -> Bool -> Bool
True  || _      = True
False || x      = x
 

--- Negation on Booleans.
not             :: Bool -> Bool
not True        = False
not False       = True

--- Useful name for the last condition in a sequence of conditional equations.
otherwise       :: Bool
otherwise       = True


--- The standard conditional. It suspends if the condition is a free variable.
if_then_else           :: Bool -> a -> a -> a
if_then_else b t f = ifThenElse (ensureNotFree b) t f
 where ifThenElse True  x _ = x
       ifThenElse False _ y = y


--- Ordering type. Useful as a result of comparison functions.
data Ordering = LT | EQ | GT


--- Equality on finite ground data terms.
(==)            :: a -> a -> Bool
(==) external

--- Disequality.
(/=)            :: a -> a -> Bool
x /= y          = not (x==y)


-- Pairs

--++ data (a,b) = (a,b)

--- Selects the first component of a pair.
fst             :: (a,_) -> a
fst (x,_)       = x

--- Selects the second component of a pair.
snd             :: (_,b) -> b
snd (_,y)       = y


-- Unit type
--++ data () = ()


-- Lists

--++ data [a] = [] | a : [a]

--- Computes the first element of a list.
head            :: [a] -> a
head (x:_)      = x

--- Computes the remaining elements of a list.
tail            :: [a] -> [a]
tail (_:xs)     = xs

--- Is a list empty?
null            :: [_] -> Bool
null []         = True
null (_:_)      = False

--- Concatenates two lists.
--- Since it is flexible, it could be also used to split a list
--- into two sublists etc.
(++)            :: [a] -> [a] -> [a]
[]     ++ ys    = ys
(x:xs) ++ ys    = x : xs++ys

--- Computes the length of a list.
length          :: [_] -> Int
length []       = 0
length (_:xs)   = 1 + length xs

--- List index (subscript) operator, head has index 0.
(!!)            :: [a] -> Int -> a
(x:xs) !! n | n==0      = x
            | n>0       = xs !! (n-1)

--- Map a function on all elements of a list.
map             :: (a->b) -> [a] -> [b]
map _ []        = []
map f (x:xs)    = f x : map f xs

--- Accumulates all list elements by applying a binary operator from
--- left to right. Thus,
--- <CODE>foldl f z [x1,x2,...,xn] = (...((z `f` x1) `f` x2) ...) `f` xn</CODE>
foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl _ z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

--- Accumulates a non-empty list from left to right.
foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  = foldl f x xs

--- Accumulates all list elements by applying a binary operator from
--- right to left. Thus,
--- <CODE>foldr f z [x1,x2,...,xn] = (x1 `f` (x2 `f` ... (xn `f` z)...))</CODE>
foldr            :: (a->b->b) -> b -> [a] -> b
foldr _ z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

--- Accumulates a non-empty list from right to left:
foldr1              :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]        = x
foldr1 f (x1:x2:xs) = f x1 (foldr1 f (x2:xs))

--- Filters all elements satisfying a given predicate in a list.
filter            :: (a -> Bool) -> [a] -> [a]
filter _ []       = []
filter p (x:xs)   = if p x then x : filter p xs
                           else filter p xs

--- Joins two lists into one list of pairs. If one input list is shorter than
--- the other, the additional elements of the longer list are discarded.
zip               :: [a] -> [b] -> [(a,b)]
zip []     _      = []
zip (_:_)  []     = []
zip (x:xs) (y:ys) = (x,y) : zip xs ys

--- Joins three lists into one list of triples. If one input list is shorter
--- than the other, the additional elements of the longer lists are discarded.
zip3                      :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3 []     _      _      = []
zip3 (_:_)  []     _      = []
zip3 (_:_)  (_:_)  []     = []
zip3 (x:xs) (y:ys) (z:zs) = (x,y,z) : zip3 xs ys zs

--- Joins two lists into one list by applying a combination function to
--- corresponding pairs of elements. Thus <CODE>zip = zipWith (,)</CODE>
zipWith                 :: (a->b->c) -> [a] -> [b] -> [c]
zipWith _ []     _      = []
zipWith _ (_:_)  []     = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys

--- Joins three lists into one list by applying a combination function to
--- corresponding triples of elements. Thus <CODE>zip3 = zipWith3 (,,)</CODE>
zipWith3                        :: (a->b->c->d) -> [a] -> [b] -> [c] -> [d]
zipWith3 _ []     _      _      = []
zipWith3 _ (_:_)  []     _      = []
zipWith3 _ (_:_)  (_:_)  []     = []
zipWith3 f (x:xs) (y:ys) (z:zs) = f x y z : zipWith3 f xs ys zs

--- Transforms a list of pairs into a pair of lists.
unzip               :: [(a,b)] -> ([a],[b])
unzip []            = ([],[])
unzip ((x,y):ps)    = (x:xs,y:ys) where (xs,ys) = unzip ps

--- Transforms a list of triples into a triple of lists.
unzip3              :: [(a,b,c)] -> ([a],[b],[c])
unzip3 []           = ([],[],[])
unzip3 ((x,y,z):ts) = (x:xs,y:ys,z:zs) where (xs,ys,zs) = unzip3 ts

--- Concatenates a list of lists into one list.
concat            :: [[a]] -> [a]
concat l          = foldr (++) [] l

--- Maps a function from elements to lists and merges the result into one list.
concatMap         :: (a -> [b]) -> [a] -> [b]
concatMap f       = concat . map f

--- Infinite list of repeated applications of a function f to an element x.
--- Thus, <CODE>iterate f x = [x, f x, f (f x),...]</CODE>
iterate           :: (a -> a) -> a -> [a]
iterate f x       = x : iterate f (f x)

--- Infinite list where all elements have the same value.
--- Thus, <CODE>repeat x = [x, x, x,...]</CODE>
repeat            :: a -> [a]
repeat x          = x : repeat x

--- List of length n where all elements have the same value.
replicate         :: Int -> a -> [a]
replicate n x     = take n (repeat x)

--- Returns prefix of length n.
take              :: Int -> [a] -> [a]
take n l          = if n<=0 then [] else takep n l
   where takep _ []     = []
         takep m (x:xs) = x : take (m-1) xs

--- Returns suffix without first n elements.
drop              :: Int -> [a] -> [a]
drop n l          = if n<=0 then l else dropp n l
   where dropp _ []     = []
         dropp m (_:xs) = drop (m-1) xs

--- (splitAt n xs) is equivalent to (take n xs, drop n xs)
splitAt           :: Int -> [a] -> ([a],[a])
splitAt n l       = if n<=0 then ([],l) else splitAtp n l
   where splitAtp _ []     = ([],[])
         splitAtp m (x:xs) = let (ys,zs) = splitAt (m-1) xs in (x:ys,zs)

--- Returns longest prefix with elements satisfying a predicate.
takeWhile          :: (a -> Bool) -> [a] -> [a]
takeWhile _ []     = []
takeWhile p (x:xs) = if p x then x : takeWhile p xs else []

--- Returns suffix without takeWhile prefix.
dropWhile          :: (a -> Bool) -> [a] -> [a]
dropWhile _ []     = []
dropWhile p (x:xs) = if p x then dropWhile p xs else x:xs

--- (span p xs) is equivalent to (takeWhile p xs, dropWhile p xs)
span               :: (a -> Bool) -> [a] -> ([a],[a])
span _ []          = ([],[])
span p (x:xs)
       | p x       = let (ys,zs) = span p xs in (x:ys, zs)
       | otherwise = ([],x:xs)

--- (break p xs) is equivalent to (takeWhile (not.p) xs, dropWhile (not.p) xs).
--- Thus, it breaks a list at the first occurrence of an element satisfying p.
break              :: (a -> Bool) -> [a] -> ([a],[a])
break p            = span (not . p)

--- Breaks a string into a list of lines where a line is terminated at a
--- newline character. The resulting lines do not contain newline characters.
lines        :: String -> [String]
lines []     = []
lines (x:xs) = let (l,xs_l) = splitline (x:xs) in l : lines xs_l
 where splitline []     = ([],[])
       splitline (c:cs) = if c=='\n'
                          then ([],cs)
                          else let (ds,es) = splitline cs in (c:ds,es)

--- Concatenates a list of strings with terminating newlines.
unlines    :: [String] -> String
unlines ls = concatMap (++"\n") ls

--- Breaks a string into a list of words where the words are delimited by
--- white spaces.
words      :: String -> [String]
words s    = let s1 = dropWhile isSpace s
              in if s1=="" then []
                           else let (w,s2) = break isSpace s1
                                 in w : words s2
 where
   isSpace c = c == ' '  || c == '\t' || c == '\n' || c == '\r'

--- Concatenates a list of strings with a blank between two strings.
unwords    :: [String] -> String
unwords ws = if ws==[] then []
                       else foldr1 (\w s -> w ++ ' ':s) ws

--- Reverses the order of all elements in a list.
reverse    :: [a] -> [a]
reverse    = foldl (flip (:)) []

--- Computes the conjunction of a Boolean list.
and        :: [Bool] -> Bool
and        = foldr (&&) True

--- Computes the disjunction of a Boolean list.
or         :: [Bool] -> Bool
or         = foldr (||) False

--- Is there an element in a list satisfying a given predicate?
any        :: (a -> Bool) -> [a] -> Bool
any p      = or . map p

--- Is a given predicate satisfied by all elements in a list?
all        :: (a -> Bool) -> [a] -> Bool
all p      = and . map p

--- Element of a list?
elem       :: a -> [a] -> Bool
elem x     = any (x==)

--- Not element of a list?
notElem    :: a -> [a] -> Bool
notElem x  = all (x/=)

--- Looks up a key in an association list.
lookup            :: a -> [(a,b)] -> Maybe b
lookup _ []       = Nothing
lookup k ((x,y):xys)
      | k==x      = Just y
      | otherwise = lookup k xys

--- Generates an infinite sequence of ascending integers.
enumFrom               :: Int -> [Int]                   -- [n..]
enumFrom n             = n : enumFrom (n+1)

--- Generates an infinite sequence of integers with a particular in/decrement.
enumFromThen           :: Int -> Int -> [Int]            -- [n1,n2..]
enumFromThen n1 n2     = iterate ((n2-n1)+) n1

--- Generates a sequence of ascending integers.
enumFromTo             :: Int -> Int -> [Int]            -- [n..m]
enumFromTo n m         = if n>m then [] else n : enumFromTo (n+1) m

--- Generates a sequence of integers with a particular in/decrement.
enumFromThenTo         :: Int -> Int -> Int -> [Int]     -- [n1,n2..m]
enumFromThenTo n1 n2 m = takeWhile p (enumFromThen n1 n2)
                         where p x | n2 >= n1  = (x <= m)
                                   | otherwise = (x >= m)


data Char
type String = [Char]

--- Converts a character into its ASCII value.
ord :: Char -> Int
ord external

--- Converts an ASCII value into a character.
chr :: Int -> Char
chr external


-- Types of primitive arithmetic functions and predicates
data Int


--- Adds two integers.
(+)   :: Int -> Int -> Int
(+) external

--- Subtracts two integers.
(-)   :: Int -> Int -> Int
(-) external

--- Multiplies two integers.
(*)   :: Int -> Int -> Int
(*) external

--- Integer division. The value is the integer quotient of its arguments
--- and always truncated towards zero.
--- Thus, the value of <code>13 `div` 5</code> is <code>2</code>,
--- and the value of <code>-15 `div` 4</code> is <code>-3</code>.
div   :: Int -> Int -> Int
div external

--- Integer remainder. The value is the remainder of the integer division and
--- it obeys the rule <code>x `mod` y = x - y * (x `div` y)</code>.
--- Thus, the value of <code>13 `mod` 5</code> is <code>3</code>,
--- and the value of <code>-15 `mod` 4</code> is <code>-3</code>.
mod   :: Int -> Int -> Int
mod external

--- Unary minus. Usually written as "- e".
negate :: Int -> Int
negate x = 0 - x

--- Is one integer less than another?
(<)   :: Int -> Int -> Bool
(<) external

--- Is one integer less than another?
(>)   :: Int -> Int -> Bool
(>) external

--- Is one integer less than or equal to another?
(<=)  :: Int -> Int -> Bool
(<=) external

--- Is one integer greater than or equal to another?
(>=)  :: Int -> Int -> Bool
(>=) external


data Float


-- Constraints
--++ data Success = Success
data Success

--- The equational constraint.
--- (e1 =:= e2) is satisfiable if both sides e1 and e2 can be
--- reduced to a unifiable data term (i.e., a term without defined
--- function symbols).
(=:=)   :: a -> a -> Success
(=:=) external

--- The always satisfiable constraint.
success :: Success
success external

--- Concurrent conjunction on constraints.
--- An expression like (c1 & c2) is evaluated by evaluating
--- the constraints c1 and c2 in a concurrent manner.
(&)     :: Success -> Success -> Success
(&) external

--- Constrained expression.
--- An expression like (c &> e) is evaluated by first solving
--- constraint c and then evaluating e.
(&>)          :: Success -> a -> a
c &> x | c = x


-- Maybe type

data Maybe a = Nothing | Just a

maybe              :: b -> (a -> b) -> Maybe a -> b
maybe n _ Nothing  = n
maybe _ f (Just x) = f x


-- Either type

data Either a b = Left a | Right b

either               :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right x) = g x


-- Monadic IO

--++ data IO a  -- conceptually: World -> (a,World)
data IO a

--- Sequential composition of actions.
--- @param a - An action
--- @param fa - A function from a value into an action
--- @return An action that first performs a (yielding result r)
---         and then performs (fa r)
(>>=)             :: IO a -> (a -> IO b) -> IO b
(>>=) external

--- The empty action that directly returns its argument.
return            :: a -> IO a
return external

--- Sequential composition of actions.
--- @param a1 - An action
--- @param a2 - An action
--- @return An action that first performs a1 and then a2
(>>)              :: IO _ -> IO b        -> IO b
a >> b            = a >>= (\_ -> b)

--- The empty action that returns nothing.
done              :: IO ()
done              = return ()

--- An action that puts its character argument on standard output.
putChar           :: Char -> IO ()
putChar external

--- An action that reads a character from standard output and returns it.
getChar           :: IO Char
getChar external

--- An action that (lazily) reads a file and returns its contents.
readFile          :: String -> IO String
readFile external

--- An action that writes a file.
--- @param filename - The name of the file to be written.
--- @param contents - The contents to be written to the file.
writeFile         :: String -> String -> IO ()
writeFile external

--- An action that appends a string to a file.
--- It behaves like writeFile if the file does not exist.
--- @param filename - The name of the file to be written.
--- @param contents - The contents to be appended to the file.
appendFile        :: String -> String -> IO ()
appendFile external

--- Catches a possible failure during the execution of an I/O action.
--- <CODE>(catchFail act err)</CODE>:
--- apply action <CODE>act</CODE> and, if it fails,
--- apply action <CODE>err</CODE>
catchFail         :: IO a -> IO a -> IO a
catchFail external

--- Action to print a string on stdout.
putStr            :: String -> IO ()
putStr []         = done
putStr (c:cs)     = putChar c >> putStr cs
 
--- Action to print a string with a newline on stdout.
putStrLn          :: String -> IO ()
putStrLn cs       = putStr cs >> putChar '\n'

--- Action to read a line from stdin.
getLine           :: IO String
getLine           = do c <- getChar
                       if c=='\n' then return []
                                  else do cs <- getLine
                                          return (c:cs)

--- Converts an arbitrary term into an external string representation.
show    :: _ -> String
show external

--- Converts a term into a string and prints it.
print   :: _ -> IO ()
print t = putStrLn (show t)

--- Solves a constraint as an I/O action.
--- Note: the constraint should be always solvable in a deterministic way
doSolve :: Success -> IO ()
doSolve constraint | constraint = done


-- IO monad auxiliary functions:

--- Executes a sequence of I/O actions and collects all results in a list.
sequenceIO       :: [IO a] -> IO [a]
sequenceIO []     = return []
sequenceIO (c:cs) = do x  <- c
                       xs <- sequenceIO cs
                       return (x:xs)

--- Executes a sequence of I/O actions and ignores the results.
sequenceIO_        :: [IO _] -> IO ()
sequenceIO_         = foldr (>>) done

--- Maps an I/O action function on a list of elements.
--- The results of all I/O actions are collected in a list.
mapIO             :: (a -> IO b) -> [a] -> IO [b]
mapIO f            = sequenceIO . map f

--- Maps an I/O action function on a list of elements.
--- The results of all I/O actions are ignored.
mapIO_            :: (a -> IO _) -> [a] -> IO ()
mapIO_ f           = sequenceIO_ . map f


----------------------------------------------------------------
-- Non-determinism:

--- Non-deterministic choice <EM>par excellence</EM>.
--- The value of <EM>x ? y</EM> is either <EM>x</EM> or <EM>y</EM>.
--- @param x - The right argument.
--- @param y - The left argument.
--- @return either <EM>x</EM> or <EM>y</EM> non-deterministically.
(?)   :: a -> a -> a
x ? _ = x
_ ? y = y

----------------------------------------------------------------
-- Encapsulated search:

--- Basic search control operator.
try     :: (a->Success) -> [a->Success]
try external

--- Inject operator which adds the application of the unary
--- procedure p to the search variable to the search goal
--- taken from Oz. p x comes before g x to enable a test+generate
--- form in a sequential implementation.
inject  :: (a->Success) -> (a->Success) -> (a->Success) 
inject g p = \x -> p x & g x

--- Computes all solutions via a left-to-right strategy.
--
-- Works as the following algorithm:
--
-- solveAll g = evalResult (try g)
--         where
--           evalResult []      = []
--           evalResult [s]     = [s]
--           evalResult (a:b:c) = concatMap solveAll (a:b:c)
--
-- The following solveAll algorithm is faster.
-- For comparison we have solveAll2, which implements the above algorithm.

solveAll     :: (a->Success) -> [a->Success]
solveAll g = evalall (try g)
  where
    evalall []      = []
    evalall [a]     = [a] 
    evalall (a:b:c) = evalall3 (try a) (b:c)

    evalall2 []    = []
    evalall2 (a:b) = evalall3 (try a) b
    
    evalall3 []      b  = evalall2 b
    evalall3 [l]     b  = l : evalall2 b
    evalall3 (c:d:e) b  = evalall3 (try c) (d:e ++b)


solveAll2  :: (a->Success) -> [a->Success]
solveAll2 g = evalResult (try g)
        where
          evalResult []      = []
          evalResult [s]     = [s]
          evalResult (a:b:c) = concatMap solveAll2 (a:b:c)


--- Gets the first solution via left-to-right strategy.
once :: (a->Success) -> (a->Success)
once g = head (solveAll g)

--- Tries to find a solution to a search goal via a fair search.
--- Fails if there is no solution.
tryone         :: (a->Success) -> a
tryone         eval choice
tryone g | g x = x  where x free

--- Searches for one solution via a fair strategy ("tryone").
--- To control failure and to return the solution in a lambda abstraction,
--- we encapsulate the search with "solveAll".
one     :: (a->Success) -> [a->Success]
one g   = solveAll (\x -> x =:= tryone g)


--- Searches the first solution that meets a specified condition.
--- "pred" must be a unary Boolean function.
condSearch        :: (a->Success) -> (a->Bool) -> [a->Success]
condSearch g pred = one (\x -> g x & pred x =:= True)


--- Gets the best solution via left-to-right strategy according to
--- a specified operator that can always take a decision which
--- of two solutions is better.
--- In general, the comparison operation should be rigid in its arguments!
best           :: (a->Success) -> (a->a->Bool) -> [a->Success]
best g compare = bestHelp [] (try g) []
 where
   bestHelp [] []     curbest = curbest
   bestHelp [] (y:ys) curbest = evalY (try (constrain y curbest)) ys curbest
   bestHelp (x:xs) ys curbest = evalX (try x) xs ys curbest
   
   evalY []        ys curbest = bestHelp [] ys curbest
   evalY [newbest] ys _       = bestHelp [] ys [newbest]
   evalY (c:d:xs)  ys curbest = bestHelp (c:d:xs) ys curbest
   
   evalX []        xs ys curbest = bestHelp xs ys curbest
   evalX [newbest] xs ys _       = bestHelp [] (xs++ys) [newbest]
   evalX (c:d:e)   xs ys curbest = bestHelp ((c:d:e)++xs) ys curbest
   
   constrain y []        = y
   constrain y [curbest] =
       inject y (\v -> let w free in curbest w & compare v w =:= True)


--- Gets all solutions via left-to-right strategy and unpack
--- the values from the lambda-abstractions.
--- Similar to Prolog's findall.
findall :: (a->Success) -> [a]
findall g = map unpack (solveAll g)


--- Gets the first solution via left-to-right strategy
--- and unpack the values from the search goals.
findfirst :: (a->Success) -> a
findfirst g = head (findall g)

--- Shows the solution of a solved constraint.
browse  :: (_->Success) -> IO ()
browse g = putStr (show (unpack g))

--- Unpacks solutions from a list of lambda abstractions and write 
--- them to the screen.
browseList :: [_ -> Success] -> IO ()
browseList [] = done
browseList (g:gs) = browse g >> putChar '\n' >> browseList gs


--- Unpacks a solution's value from a (solved) search goal.
unpack  :: (a -> Success) -> a
unpack g | g x  = x  where x free


--- Identity function used by the partial evaluator
--- to mark expressions to be partially evaluated.
PEVAL   :: a -> a
PEVAL x = x

-- Only for internal use:
-- Represenation of higher-order applications in FlatCurry.
apply :: (a->b) -> a -> b
apply external

-- Only for internal use:
-- Representation of conditional rules in FlatCurry.
cond :: Success -> a -> a
cond external

-- Only for internal use:
-- Representation of committed choice in FlatCurry.
commit :: a -> a
commit external

-- the end
