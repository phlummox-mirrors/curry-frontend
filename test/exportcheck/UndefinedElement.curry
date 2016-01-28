-- Should issue the following error:
--
-- test/exportcheck/UndefinedElement.curry, line 6.32:
--     `foo' is not a constructor or label of type `Bool'
--
module UndefinedElement (Bool (foo)) where
