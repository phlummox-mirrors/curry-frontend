-- This module belongs to the ticket 1324
module MissingCaseCompletion where

-- The missing constructor False should not be expanded to "False -> Failed".
-- Instead it should be omitted.
f :: Bool -> Int
f b = case b of
           True -> 1

-- The catch all pattern should be expanded to "False -> 0".
g :: Bool -> Int
g b = case b of
           True -> 1
           _    -> 0

-- The catch all pattern should be expanded to "False -> failed"
h :: Bool -> Int
h b = case b of
           True -> 1
           _    -> failed

-- To summarize the issue: If a case expression explicitely ignores at least one
-- constructor (i.e. it does not enumerate everyone and does not use a default
-- pattern), do not fill up with missing constructors and failed expressions.