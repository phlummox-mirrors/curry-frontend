-- Should issue the following error:
--
-- test/exportcheck/OutsideTypeLabel.curry, line 7.26:
--     Label `value' outside type export in export list
--     Use `OutsideTypeLabel.Id (value)' instead
--
module OutsideTypeLabel (value) where

data Id a = Id { value :: a }
