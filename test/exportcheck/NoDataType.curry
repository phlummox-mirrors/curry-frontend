-- Should issue the following error:
--
-- test/exportcheck/NoDataType.curry, line 6.20:
--     `Foo' is not a data type
--
module NoDataType (Foo ()) where

type Foo a = a
