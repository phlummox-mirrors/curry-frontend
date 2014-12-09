-- Loading this module (in pakcs) leads to cymake <<loop>>.
-- it might be interesting that the last line is important for this error to
-- occur; if the last line is omitted or changed to "i = 3" then the expected
-- error "recursive synonym types" is properly printed.

module Bug489 where

type A = B
type B = A

i = Just ()
