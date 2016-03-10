-- Should issue the following error:
--
-- test/exportcheck/AmbiguousName.curry, line 9.23:
--     Ambiguous name `not'
--     It could refer to:
--       `Prelude.not'
--       `Bool.not'
--
module AmbiguousName (not) where

import Bool
