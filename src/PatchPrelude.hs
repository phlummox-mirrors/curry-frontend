module PatchPrelude where


import Base (isImportDecl)
import FlatCurry
import Position
import Ident
import PathUtils


-- the prelude has to be extended by data declarations for list and tuples

patchPreludeFCY :: Prog -> Prog
patchPreludeFCY (Prog name imports types funcs ops)
   | name == "prelude"
     = Prog name [] (prelude_types_fcy ++ types) funcs ops
   | otherwise
     = Prog name imports types funcs ops

prelude_types_fcy :: [TypeDecl]
prelude_types_fcy =
  [Type ("prelude","()") Public [] [(Cons ("prelude","()") 0 Public [])],
   Type ("prelude","[]") Public [0] 
        [Cons ("prelude","[]") 0 Public [],
         Cons ("prelude",":") 2 Public 
              [TVar 0, TCons ("prelude","[]") [TVar 0]]]] ++
  map tupleType [2..maxTupleArity]

tupleType ar = let tuplecons = "("++take (ar-1) (repeat ',')++")" in
  Type ("prelude",tuplecons) Public [0..ar-1]
       [Cons ("prelude",tuplecons) ar Public (map TVar [0..ar-1])]

-- Maximal arity of tuples:
maxTupleArity = 15


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

