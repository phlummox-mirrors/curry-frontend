> module HeaderTable where

> import CurrySyntax
> import Ident
> import Env
> import Maybe


-------------------------------------------------------------------------------

Data type for representing a table to store top level declaration headers for
data types, type synonyms, functions and operators.

> type HeaderTable = Env Ident [DeclHeader]


-------------------------------------------------------------------------------

Generates a table containing header information for all top level declarations,
i.e. data types, type synonyms, functions and operators.

> headerTable :: Module -> HeaderTable
> headerTable (Module mident expspec decls)
>    = foldl (genDeclHeader mident exports) emptyEnv decls
>  where
>    exports = maybe Nothing (\ (Exporting _ exports) -> Just exports) expspec


> containsHeader :: Ident -> HeaderTable -> Bool
> containsHeader ident table = isJust (lookupEnv ident table)


-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
Private declarations

Code:
   (DataDeclHeader <id> <is exported?> <arity> <constructor ids>)
   (TypeSynHeader  <id> <is exported?> <parameters> <type expression>)
   (ConsDeclHeader <id> <is exported?> <arity> <data type>)
   (OpDeclHeader   <id> <is exported?> <fixity> <precedence>)
   (FuncDeclHeader <id> <is exported?> <arity>)

> data DeclHeader = 
>      DataDeclHeader Bool Int [Ident]
>    | TypeSynHeader  Bool [Ident] TypeExpr
>    | ConsDeclHeader Bool Int Ident
>    | OpDeclHeader   Bool Infix Int
>    | FuncDeclHeader Bool Int



Empty header entries:

-> emptyDataDecl ident = DataDeclHeader ident False 0 []
-> emptyTypeSyn  ident = TypeSynHeader  ident False [] (VariableType (mkIdent "a"))
-> emptyConsDecl ident = ConsDeclHeader ident False 0 (VariableType (mkIdent "a"))

-------------------------------------------------------------------------------

> genDeclHeader :: ModuleIdent -> Maybe [Export] -> HeaderTable -> Decl -> HeaderTable
> genDeclHeader mident exps table (ImportDecl _ _ _ _ _) = table
> genDeclHeader mident exps table (InfixDecl _ fixity prec idents)
>    = foldl (insertOpDeclHeader mident exps fixity prec) table idents -- TODO!
> genDeclHeader mident exps table (DataDecl _ ident _ cdecls)
>    = insertDataDeclHeader mident exps cdecls table ident -- TODO!
> genDeclHeader mident exps table (NewtypeDecl _ _ _ cdecl)
>    = -- Nachschauen, wie dies bearbeitet werden kann
> genDeclHeader mident exps table (TypeDecl _ ident params typeexpr)
>    = insertTypeSynHeader mident exps params typeexpr table ident -- TODO!
> genDeclHeader mident exps table (TypeSig _ _ _) = table
> genDeclHeader mident exps table (EvalAnnot _ _ _) = table
> genDeclHeader mident exps table (FunctionDecl _ ident equat)
>    | isInfixOp ident && not (containsOpDeclHeader ident table) -- TODO!
>      = insertOpDeclHeader mident exps Infix 0 table ident
>    | not (containsFuncDeclHeader ident table)
>      = insertFuncDeclHeader mident exps (getArityFromEquat equat) table ident -- TODO!
>    | otherwise
>      = table
> genDeclHeader mident exps table (ExternalDecl _ _ _ ident typeexpr)
>    | isInfixOp ident && not (containsOpDeclHeader ident table)
>      = insertOpDeclHeader mident exps Infix 0 table ident
>    | not (containsFuncDeclHeader ident table)
>      = insertFuncDeclHeader mident exps (getArityFromTypeExpr typeexpr) table ident -- TODO!
>    | otherwise
>      = table
> genDeclHeader mident exps table (


-- Andere Idee:
-- Erzeuge folgende Listen
--   - ExportListe [Ident]
--   - OpListe [OpHeader]
--   - TypeSyn-Liste [TypeSynHeader]
--   - Symbol-Liste [SymbolHeader]


-------------------------------------------------------------------------------

Modifies existing headers using a modifier function.

> modifyHeader :: HeaderTable -> Ident -> (DeclHeader -> DeclHeader) -> HeaderTable
> modifyHeader table ident modify 
>    = maybe table 
>      (\es -> bindEnv ident (map modify es) table) 
>      (lookupEnv ident table)

-------------------------------------------------------------------------------
-------------------------------------------------------------------------------
