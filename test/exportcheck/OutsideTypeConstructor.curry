-- Should issue the following error:
--
-- test/exportcheck/OutsideTypeConstructor.curry, line 7.32:
--     Data constructor `False' outside type export in export list
--     Use `Prelude.Bool (False)' instead
--
module OutsideTypeConstructor (False) where
