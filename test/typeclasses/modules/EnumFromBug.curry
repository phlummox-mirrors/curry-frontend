

import TCPrelude
import Prelude ()

--- Generates a sequence of integers with a particular in/decrement.
enumFromThenTo1         :: Char -> Char -> Char -> [Char]     -- [n1,n2..m]
enumFromThenTo1 n1 n2 m = takeWhile p [] -- (enumFromThen_ n1 n2)
  where p x {-| n2 >= n1-}  = (x <= m)
             -- | otherwise = (x >= m)


--- Generates a sequence of integers with a particular in/decrement.
enumFromThenTo2         :: Char -> Char -> Char -> [Char]     -- [n1,n2..m]
enumFromThenTo2 n1 n2 m = takeWhile p [] -- (enumFromThen_ n1 n2)
  where p x | n2 >= n1  = (x <= m)
            | otherwise = (x >= m)