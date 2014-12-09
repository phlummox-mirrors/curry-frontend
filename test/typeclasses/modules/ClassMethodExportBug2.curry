

module ClassMethodExportBug2
  (funC
  ) where


  
class Enum a where
  funC       :: a -> [a]
