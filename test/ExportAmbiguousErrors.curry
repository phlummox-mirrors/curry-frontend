module ExportAmbiguousErrors (Bool, Prelude.Bool, not, Prelude.not) where

import Prelude

data Bool = False | True

not :: Bool -> Bool
not False = True
not True  = False
