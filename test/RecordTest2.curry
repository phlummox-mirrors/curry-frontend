module RecordTest2 where

import RecursiveRecords

showR :: R Int -> String
showR r = show (r :> f1) ++ (r :> f2)
