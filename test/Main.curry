import qualified Set

join s1 s2 = Set.union s1 s2

--> front-end error:
--> cymake: internal error: renameInfo: missing arity of List.union

--> everything works if "qualified" is removed from the import

