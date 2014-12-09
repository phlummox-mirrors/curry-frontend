
class C a where
  fun :: a -> Bool
  fun2 :: a -> a

-- two errors:
--   * type signature too general
--   * error output pretty printing: Type signature: C Bool => => Bool
testExplTyped3 x = x :: C Bool => Bool