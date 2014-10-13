{-# LANGUAGE Records #-}
module RecordTest where

type Record =
  { intField  :: Int
  , boolField :: Bool
  }

empty = { intField := 0, boolField := False }

full = { intField := 1, boolField := True }

expr = empty :> intField + 1 == 0

match { intField = i | _ } = i

-- int :: { intField :: Int | a }
-- int = { intField := 0 }

type Record2 =
  { intField2  :: Int
  , boolField2 :: Bool
  }

test = { intField2 := 0, boolField2 := True }
