module PatchPrelude where


import Base (isImportDecl)
import FlatCurry
import Position
import Ident
import PathUtils


-------------------------------------------------------------------------------

patchPreludeSource :: FilePath -> String -> String
patchPreludeSource fn src
   | (basename (rootname fn)) == "prelude"
     = src ++ "\n\n" ++ unlines preludePatchSource
   | otherwise
     = src


patchPreludeFCY :: Prog -> Prog
patchPreludeFCY (Prog name imports types funcs ops)
   | name == "prelude"
     = Prog name [] (prelude_types_fcy ++ types) funcs ops
   | otherwise
     = Prog name imports types funcs ops


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

preludePatchSource :: [String]
preludePatchSource
   = ["data Int", 
      "data Float",
      "data Char",
      "data Success",
      "data IO a",
      "data Bool = True | False",
      "type String = [Char]"]


prelude_types_fcy :: [TypeDecl]
prelude_types_fcy = [(Type ("prelude","()") Public [] 
		      [(Cons ("prelude","()") 0 Public [])]),
		     (Type ("prelude","[]") Public [0] 
		      [(Cons ("prelude","[]") 0 Public []),
		       (Cons ("prelude",":") 2 Public 
			[(TVar 0),(TCons ("prelude","[]") [(TVar 0)])])]),
		     (Type ("prelude","(,)") Public [0,1] 
		      [(Cons ("prelude","(,)") 2 Public 
			[(TVar 0),(TVar 1)])]),
		     (Type ("prelude","(,,)") Public [0,1,2]
		      [(Cons ("prelude","(,,)") 3 Public 
			[(TVar 0),(TVar 1),(TVar 2)])]),
		     (Type ("prelude","(,,,)") Public [0,1,2,3] 
		      [(Cons ("prelude","(,,,)") 4 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3)])]),
		     (Type ("prelude","(,,,,)") Public [0,1,2,3,4] 
		      [(Cons ("prelude","(,,,,)") 5 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),(TVar 4)])]),
		     (Type ("prelude","(,,,,,)") Public [0,1,2,3,4,5] 
		      [(Cons ("prelude","(,,,,,)") 6 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),(TVar 4),
			 (TVar 5)])]),
		     (Type ("prelude","(,,,,,,)") Public [0,1,2,3,4,5,6] 
		      [(Cons ("prelude","(,,,,,,)") 7 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6)])]),
		     (Type ("prelude","(,,,,,,,)") Public [0,1,2,3,4,5,6,7] 
		      [(Cons ("prelude","(,,,,,,,)") 8 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7)])]),
		     (Type ("prelude","(,,,,,,,,)") Public [0,1,2,3,4,5,6,7,8] 
		      [(Cons ("prelude","(,,,,,,,,)") 9 Public
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8)])]),
		     (Type ("prelude","(,,,,,,,,,)") Public 
		      [0,1,2,3,4,5,6,7,8,9] 
		      [(Cons ("prelude","(,,,,,,,,,)") 10 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),(TVar 9)])]),
		     (Type ("prelude","(,,,,,,,,,,)") Public 
		      [0,1,2,3,4,5,6,7,8,9,10] 
		      [(Cons ("prelude","(,,,,,,,,,,)") 11 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),
			 (TVar 9),(TVar 10)])]),
		     (Type ("prelude","(,,,,,,,,,,,)") Public 
		      [0,1,2,3,4,5,6,7,8,9,10,11] 
		      [(Cons ("prelude","(,,,,,,,,,,,)") 12 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7),(TVar 8),
			 (TVar 9),(TVar 10),(TVar 11)])]),
		     (Type ("prelude","(,,,,,,,,,,,,)") Public 
		      [0,1,2,3,4,5,6,7,8,9,10,11,12] 
		      [(Cons ("prelude","(,,,,,,,,,,,,)") 13 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7),
			 (TVar 8),(TVar 9),(TVar 10),(TVar 11),(TVar 12)])]),
		     (Type ("prelude","(,,,,,,,,,,,,,)") Public 
		      [0,1,2,3,4,5,6,7,8,9,10,11,12,13] 
		      [(Cons ("prelude","(,,,,,,,,,,,,,)") 14 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7),
			 (TVar 8),(TVar 9),(TVar 10),(TVar 11),
			 (TVar 12),(TVar 13)])]),
		     (Type ("prelude","(,,,,,,,,,,,,,,)") Public 
		      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] 
		      [(Cons ("prelude","(,,,,,,,,,,,,,,)") 15 Public 
			[(TVar 0),(TVar 1),(TVar 2),(TVar 3),
			 (TVar 4),(TVar 5),(TVar 6),(TVar 7),
			 (TVar 8),(TVar 9),(TVar 10),(TVar 11),
			 (TVar 12),(TVar 13),(TVar 14)])])]


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

