--- Internal error when function and label identifier coincide
--- Redmine - curry-frontend - bug #1276

data Record = Record { id :: Int }

id :: a -> a
id x = x
