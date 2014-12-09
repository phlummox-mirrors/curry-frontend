
module ArbTypeSyn where

type Fun x = x -> x

class Arb a where
  arb :: Fun a

instance Arb Bool where
  arb True = False


