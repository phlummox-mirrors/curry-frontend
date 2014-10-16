type R a = { f1 :: a, f2 :: String }


-- type Person = { name :: String, age :: Int, friends :: [Person] }
--
-- john = { name := "John", age := 21, friends := [tim] }
--
-- tim = { name := "Tim", age := 26, friends := [john] }
--
-- ann = { name := "Ann", age := 20, friends := [john,ann] }
--
-- getFriends :: Person -> [Person]
-- getFriends p = p :> friends
--
-- addFriend :: Person -> Person -> Person
-- addFriend p friend = { friends := friend : (getFriends p) | p }
--
-- getNames :: Person -> [String]
-- getNames { friends = fs | _ } = map (\p -> p :> name) fs
--
-- --------------------------------------------------------------------------------
--
-- type R1 = { r2 :: R2 }
-- type R2 = { r1 :: R1 }
--
-- rec1 = { r2 := rec2 }
-- rec2 = { r1 := rec1 }
--
-- type R3 = { f1 :: TSR3 }
-- type TSR3 = R3