
module ClassInstanceTypeInScope6 where

class A a where


data Char = Char

-- no error
instance A Char where

