

module InstancesExportBug () where

-- import Prelude as P

class Eq a where

data T a

instance Eq [a] where

instance Eq (a, b) where

instance Eq (a, b, c) where

instance Eq () where

instance Eq (a -> b) where

instance Eq (T a) where

