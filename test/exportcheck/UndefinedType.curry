-- Should issue the following error:
--
-- test/exportcheck/UndefinedType.curry, line 6.23:
--     Undefined Type `Foo' in export list
--
module UndefinedType (Foo ()) where
