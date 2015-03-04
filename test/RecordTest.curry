module RecordTest (Agent, lastName, trueIdentity, mike) where

data Person = Person { firstName :: String, lastName :: String }
            | Agent  { lastName :: String, trueIdentity :: Person }

mike :: Person
mike = Person { firstName = "Mike", lastName = "Smith" }