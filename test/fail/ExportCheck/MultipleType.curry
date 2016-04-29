-- Should issue the following error:
--
-- test/exportcheck/MultipleType.curry, line 8.22:
--     Multiple exports of type `Bool' at:
--       line 8.22
--       line 8.33
--
module MultipleType (Bool.Bool, Prelude.Bool) where

import qualified Bool
