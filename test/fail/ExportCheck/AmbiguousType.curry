-- Should issue the following error:
--
-- test/exportcheck/AmbiguousType.curry, line 9.23:
--     Ambiguous type `Bool'
--     It could refer to:
--       `Prelude.Bool'
--       `Bool.Bool'
--
module AmbiguousType (Bool ()) where

import Bool
