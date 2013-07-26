
module HiddenClasses2 where

import HiddenClasses1 (D(..))

class C a where

test :: C a => a -> a
test x = x

test2 :: HiddenClasses2.C a => a -> a
test2 x = x

