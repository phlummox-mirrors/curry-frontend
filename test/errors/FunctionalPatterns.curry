type Foo = { foo :: Bool }

f1 (id v@x) = x
f2 (id ~(v:vs)) = v
f3 (id { foo = bar }) = bar
