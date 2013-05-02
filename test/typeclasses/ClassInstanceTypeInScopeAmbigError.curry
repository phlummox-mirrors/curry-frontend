
module ClassInstanceTypeInScopeAmbigError where

class A a where


data Char = Char

instance A Char where

