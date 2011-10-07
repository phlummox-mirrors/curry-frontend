module RecordTest where

type Record =
  { intField  :: Int
  , boolField :: Bool
  }

empty = { intField = 0, boolField = False }

full = { intField = 1, boolField = True }