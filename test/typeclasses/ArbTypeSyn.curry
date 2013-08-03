
module ArbTypeSyn where

type Fun x = x -> x

class Arb a where
  arb :: Fun a

test = arb
