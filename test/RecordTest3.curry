import RecursiveRecords
import RecordTest2

r :: R Int
r = { f1 := 4, f2 := "hello" }

e = showR r

-- type R1 a b = { f1 :: a, f2 :: b }
-- type R2 = { f3 :: Int }
--
-- type R3 a b = { f5 :: a, f4 :: Maybe b }
--
-- type Person = { name :: String, age :: Int }
--
-- type Address = { person :: Person, street :: String, city :: String }
--
-- smith :: Person
-- smith = { name := "Smith", age := 20 }
--
-- a :: Address
-- a = { person := smith, street := "Main Street", city := "New York" }

-- p2 = { name := "Doe" }

-- data T = T (R3 Int)

--f :: R1 -> R1
--f x = x + 1

--g :: R3 Int -> R3 Int
--g x = not x

--r1 = { f1 := False, f2 := "" }

-- r2 :: R2
-- r2 = { f3 := Just 1 }

-- r3 :: R1 Bool String
--r3 = { f4 := Just 1, f5 := "" }

--inc :: Int -> Int
--inc = (+1)

-- e :: Maybe Bool
--sel1 = (r3 :> f5)

-- upd1 = { f1 := True | r2 }

-- upd2 = { f3 := True | r2 }

-- pat1 { name = "Smith", age = 25 } = True

-- pat2 { person = p | _} = p

--r1 :: R1
--r1 = { f1 := False, f2 := r2 }

--r3 :: R3 Int
--r3 = { f4 := "", f5 := Just 1 }

--e = { f2 := r3 | r1}

--type RR = { f6 :: RR }
