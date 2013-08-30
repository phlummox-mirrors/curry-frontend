
module LocalModuleExport (module LocalModuleExport, T(..)) where

data T a = T a
-- newtype S a = S a

type U a = T a

fun :: a -> a
fun x = x

