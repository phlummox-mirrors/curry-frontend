
module HiddenClasses2Err where

import HiddenClasses1 (D(..))

class C a where

test :: HiddenClasses1.C a => a -> a
test x = x

