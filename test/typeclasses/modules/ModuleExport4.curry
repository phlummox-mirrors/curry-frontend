
module ModuleExport4 (D(..), K1 (..), K2(..)) where

class C a where
  
class C a => D a where
  funD :: a -> a
  
class C2 a where
  
class C2 a => D2 a where
  
class K1 a where
  funK1 :: a -> a
  
class K2 a where
  
class L a where
  
