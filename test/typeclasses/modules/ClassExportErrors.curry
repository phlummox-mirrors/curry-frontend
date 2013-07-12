
module ClassExportErrors
 ( C
 , D
 , E
 , F
 , G (notExistent, notExistent2, funG1)
 , H (notExistent)
 ) where

class C a where

data C a b = C a b

class E a where

data F a = F a

class G a where
  funG1 :: a -> a

data H a = H a
