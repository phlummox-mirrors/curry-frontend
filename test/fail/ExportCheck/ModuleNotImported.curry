-- Should issue the following error:
--
-- test/exportcheck/ModuleNotImported.curry, line 6.34:
--     Module `Foo' not imported
--
module ModuleNotImported (module Foo) where
