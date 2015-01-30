module Newtype where

newtype D a = D a

access :: D a -> a
access (D a1) = a1
