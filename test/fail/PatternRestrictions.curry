{-# LANGUAGE FunctionalPatterns #-}
data Foo = Foo { foo :: Bool }

f1 (id v@x) = x
f2 (id ~(v:vs)) = v
f3 (id Foo { foo = bar }) = bar
