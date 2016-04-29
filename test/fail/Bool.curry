module Bool where

data Bool = False | True

not :: Bool -> Bool
not False = True
not True  = False
