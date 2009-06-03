module PatchPrelude where


import Base (isImportDecl)
import FlatWithSrcRefs
import Position
import Ident
import PathUtils


-- the prelude has to be extended by data declarations for list and tuples

patchPreludeFCY :: Prog -> Prog
patchPreludeFCY (Prog name imports types funcs ops)
   | name == "Prelude"
     = Prog name [] (prelude_types_fcy ++ types) funcs ops
   | otherwise
     = Prog name imports types funcs ops

prelude_types_fcy :: [TypeDecl]
prelude_types_fcy =
  [Type ("Prelude","()") Public [] [(Cons ("Prelude","()") 0 Public [])],
   Type ("Prelude","[]") Public [0] 
        [Cons ("Prelude","[]") 0 Public [],
         Cons ("Prelude",":") 2 Public 
              [TVar 0, TCons ("Prelude","[]") [TVar 0]]]] ++
  map tupleType [2..maxTupleArity]

tupleType ar = let tuplecons = "("++take (ar-1) (repeat ',')++")" in
  Type ("Prelude",tuplecons) Public [0..ar-1]
       [Cons ("Prelude",tuplecons) ar Public (map TVar [0..ar-1])]

-- Maximal arity of tuples:
maxTupleArity = 15


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

