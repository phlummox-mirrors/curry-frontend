-- record declarations
data R1 = R1 { f11, f13 :: Int, f12 :: Bool }

data R2 = R2 { f21 :: String, f22 :: R2 }

newtype R3 = R3 { f31 :: Char }

-- record constructions

r1 :: R1
r1 = R1 { f11 = 42, f12 = True, f13 = 4 }

r2 :: R2
r2 = R2 { f21 = "hello", f22 = r2 }

r3 = R3 'c'

-- record selection

answer :: Int
answer = f11 r1

innerRecord :: R2
innerRecord = f22 r2

c :: Char
c = f31 r3

-- record update

r1' :: R1
r1' = R1 { f12 = False }

r2' :: R2
r2' = R2 { f21 = "bye" }

-- pattern matching on records

isAnswer :: R1 -> Bool
isAnswer (R1 { f11 = 42, f12 = b }) = b

firstLetter :: R2 -> Char
firstLetter (R2 { f21 = (c:cs) }) = c
firstLetter _                     = 'f'
