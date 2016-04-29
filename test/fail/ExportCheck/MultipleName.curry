-- Should issue the following error:
--
-- test/exportcheck/MultipleName.curry, line 8.22:
--     Multiple exports of name `not' at:
--       line 8.22
--       line 8.32
--
module MultipleName (Bool.not, Prelude.not) where

import qualified Bool
