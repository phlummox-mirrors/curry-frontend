

module ModulesExportInstances where

class C a where
  funC :: a -> a

instance C Bool where
  funC True = True
