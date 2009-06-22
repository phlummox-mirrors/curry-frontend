% -*- LaTeX -*-
% $Id: DTransform.lhs,v 1.10 2004/04/20 18:33:16 wlux Exp $
%
% 2002/04/10 19:00:00 Added emptyNode as constructor in type cTree
\nwfilename{DTransform.lhs}

\section{Transforming intermediate representation for debugging}

The purpose of this module is to convert the intermediate representation of 
a program $P$, of type {\tt Module} into the intermediate representation of a 
transformed program $P'$. 
$P'$ corresponds to the transformation of $P$ for debugging purposes. Each 
function in $P'$ computes the same values as its corresponding function in $P$,
but in addition it also returns a suitable {\em Computation Tree} representing
the computation.

\begin{verbatim}

> module DTransform(module DTransform) where
> import Ident
> import List
> import IL

\end{verbatim}

All the new and auxiliary names in the transformed module will have 
{\tt debugPrefix}
prefix to avoid conflicts with user-names. Auxiliary data types and functions
will be imported from the debug prelude, whose name is defined below, and that
will be imported by all the transformed modules.

\begin{verbatim}

> debugPrefix,debugPreludeName,debugFunctionName :: String
> debugPrefix       = "_debug#"
> debugPreludeName  = "DebugPrelude"
> debugFunctionName =  "startDebugging"


\end{verbatim}

Next is the principal  function of the module. The boolean parameter is 
{\tt True} whenever the functions of the module must be trusted. In this case
they will return empty nodes as computation trees, but still can 
include some useful trees as children.

\begin{verbatim}

> dTransform :: Bool -> Module -> Module
> dTransform trust (Module m is ds) = Module m (i:is) (debugDecls m trust ds)
>       where 
>       i   =  debugPreludeModule

\end{verbatim}

We can divide the declarations in the transformed program in five different
groups:
\begin{itemize}
\item New data types and functions: Introduced in order to represent 
      and deal with computation tress. This is done by adding de degugging
      prelude to the list of import modules, and included a new function 
      {\tt main} in the module main (the older will be renamed).
\item External declarations: The same as in the source program.
\item Data types: The same as in the source program.
\item New auxliary functions: Introduced to represent partial applications of 
      constructors and (maybe external) functions.
\item Transformed functions: The rules of the source program transformed. 
      In the final program they will return a computation tree, as well as their
      the same result they did in the source program.
\end{itemize}

\begin{verbatim}

> debugDecls :: ModuleIdent -> Bool -> [Decl] -> [Decl]
> debugDecls m  trust lDecls = 
>       externals  ++
>       types ++
>       debugAuxiliary m lTypes ++ 
>       secondPhase 
>       where
>          (types,functions,externals) = debugSplitDecls lDecls
>          lTypes = collectSymbolTypes types functions externals []
>          lExternal = map (\(ExternalDecl id cc s t) -> id) externals
>          firstPhase = debugFirstPhase  m lExternal functions
>          secondPhase =  map (debugFunction trust) firstPhase


\end{verbatim}


Some auxiliar functions widely used throughout the module

%Function that builds a qualified name from the name of the module and a string 
%standing for the name we are going to represent.
\begin{verbatim}

> newIdName :: Int -> String -> Ident
> newIdName n name =  mkIdent (debugPrefix++name++(show n))

> newModuleName :: ModuleIdent -> String -> QualIdent
> newModuleName m name = qualifyWith m (mkIdent (debugPrefix ++ name))

> debugQualPrelude :: Ident -> QualIdent
> debugQualPrelude  = qualifyWith debugPreludeModule

> debugQualPreludeName :: String  -> QualIdent
> debugQualPreludeName  name = debugQualPrelude (mkIdent name)

> debugPreludeModule :: ModuleIdent
> debugPreludeModule   = mkMIdent [debugPreludeName]

> debugFunctionqId :: QualIdent
> debugFunctionqId = debugQualPrelude (mkIdent debugFunctionName)

> debugRenameId :: String -> Ident -> Ident
> debugRenameId suffix ident =
>   renameIdent (mkIdent (debugPrefix ++ name ident ++ suffix)) (uniqueId ident)


> isPreludeFunction :: QualIdent -> Bool
> isPreludeFunction qId = maybe emptyMIdent id idModule==preludeMIdent
>       where
>       (idModule,ident) = splitQualIdent qId

\end{verbatim}

Qualified data types representing some useful types in the transformed program:
{\tt [a], (a,b), Char, [Char], CTree} and {\tt [Ctree]}. Also function for
constructing expressions of the form (a,b) and the name of function 
{\tt clean}.

\begin{verbatim}

> typeCons :: Type
> typeCons = TypeArrow (TypeVariable 0) 
>               (TypeArrow (debugTypeList (TypeVariable 0))  
>                          (debugTypeList (TypeVariable 0)))

> typeTuple :: Int -> Type
> typeTuple n = foldr TypeArrow (debugTypeTuple ts) ts
>   where ts = [TypeVariable i | i <- [0 .. n - 1]]

> debugTypeList :: Type -> Type
> debugTypeList t = TypeConstructor (qualifyWith preludeMIdent listId) [t]

> debugTypePair :: Type -> Type -> Type
> debugTypePair a b = TypeConstructor debugIdentPair [a,b]

> debugTypeTuple :: [Type] -> Type
> debugTypeTuple ts = TypeConstructor (debugIdentTuple (length ts)) ts

> debugTypeChar,debugTypeString:: Type
> debugTypeChar   = TypeConstructor (qualifyWith preludeMIdent charId) []
> debugTypeString = debugTypeList debugTypeChar


> debugTypeCTree,debugTypeLCTree,debugTypeCleanTree,debugTypeLCleanTree:: Type
> debugTypeCTree   = TypeConstructor (debugQualPreludeName "CTree") []
> debugTypeLCTree  = debugTypeList debugTypeCTree
> debugTypeCleanTree = debugTypePair debugTypeString debugTypeCTree
> debugTypeLCleanTree = debugTypeList debugTypeCleanTree

> debugTypeMainAux :: Type
> debugTypeMainAux = TypeArrow (debugTypePair (TypeVariable 0) debugTypeCTree)
>                              (TypeConstructor qSuccessId [])



> debugIdentPair :: QualIdent
> debugIdentPair = debugIdentTuple 2

> debugIdentTuple :: Int -> QualIdent
> debugIdentTuple n = qualify (tupleId n)

> debugIdentCons :: QualIdent
> debugIdentCons = qualify consId

> debugIdentNil :: QualIdent
> debugIdentNil = qualify nilId

> debugNil :: Expression
> debugNil = Constructor debugIdentNil 0

> debugBuildPairExp :: Expression -> Expression -> Expression
> debugBuildPairExp e1 e2 = Apply (Apply (Constructor debugIdentPair 2) e1) e2


> debugClean :: QualIdent 
> debugClean  = debugQualPreludeName "clean"

> debugTry :: QualIdent 
> debugTry  = debugQualPreludeName "try'"


> dEvalApply :: Expression -> Expression
> dEvalApply = Apply (Function dEvalId 1)

> dEvalId :: QualIdent
> dEvalId =  debugQualPreludeName "dEval"


> void :: Expression
> void =  Constructor (qualifyWith debugPreludeModule  (mkIdent "CTreeVoid")) 0

> emptyNode :: Expression-> Expression
> emptyNode  children = 
>          createApply ( 
>               Constructor (qualifyWith debugPreludeModule  
>                                 (mkIdent "EmptyCTreeNode")) 1)
>                        [children]


> createEmptyNode ::  [Expression] -> Expression
> createEmptyNode trees = 
>       emptyNode  clean
>       where
>       clean   = Apply (Function debugClean 1) (debugBuildList trees)


> debugBuildList :: [Expression] -> Expression
> debugBuildList l = foldr Apply  debugNil (map (Apply cons) l)
>       where
>        cons = Constructor debugIdentCons 2


> node :: Expression -> Expression -> Expression -> Expression -> Expression ->
>         Expression
> node name args result number children =
>      createApply (Constructor (qualifyWith debugPreludeModule 
>                                                (mkIdent "CTreeNode")) 5)
>                [name, args, result, number, children]

\end{verbatim}

We distinguish three classes of declarations: types, functions and externals.
Each class needs an specific treatment, and therefore we split the initial
list of declarations in three.
\begin{verbatim}

> debugSplitDecls :: [Decl] -> ([Decl],[Decl],[Decl])
> debugSplitDecls []     = ([],[],[])
> debugSplitDecls (x:xs) = case x of
>                      DataDecl     _ _ _   -> (x:types,functions,externals)
>                      NewtypeDecl  _ _ _   -> (x:types,functions,externals)
>                      FunctionDecl _ _ _ _ -> (types,x:functions,externals)
>                      ExternalDecl _ _ _ _ -> (types,functions,x:externals)
>                   where
>                       (types,functions,externals) = debugSplitDecls xs 

\end{verbatim}

The newMain is only added if we are in the module main. 
It will start de debugging process.

Its definition:

\begin{verbatim}


main.main = DebugPrelude.startDebugging 
                (\(x,ct)-> let (r,ct') = main._debug#main in x=:=r &> ct=:=ct')

\end{verbatim}

We have to introduce an auxiliary function for the lambda in the intermediate code.

\begin{verbatim}

> dAddMain :: Ident -> Module -> Module
> dAddMain goalId (Module m is ds) = Module m is (newMain goalId ++ ds)

> newMain :: Ident -> [Decl]
> newMain f = [fMain,auxMain]
>       where 
>       fMain = FunctionDecl fId [] fType fBody
>       fId   = qualifyWith emptyMIdent f
>       fType = TypeVariable 0
>       fBody = Apply (Function debugFunctionqId 1) (Function debugAuxMainId 1)
>       fType' = debugTypeMainAux
>       r   = mkIdent "r"
>       ct' = mkIdent "ct'"
>       x   = mkIdent "x"
>       ct   = mkIdent "ct"
>       param  = mkIdent "x_ct"
>       eq1 = createApply equalFunc  [Variable x, Variable r]
>       eq2 = createApply equalFunc  [Variable ct, Variable ct']        
>       equalFunc = Function (qualifyWith preludeMIdent (mkIdent "=:=")) 2
>       seqAndFunc = Function (qualifyWith preludeMIdent (mkIdent "&>")) 2
>       expression =  createApply seqAndFunc [eq1,eq2]
>       alt'     = Alt (ConstructorPattern debugIdentPair [x,ct]) expression
>       caseExpr = Case Flex (Variable param) [alt']
>       alt      = Alt (ConstructorPattern debugIdentPair [r,ct']) caseExpr
>       fBody'   = Case Rigid  (Function debugOldMainId 0) [alt]
>       auxMain = FunctionDecl debugAuxMainId [param] fType' fBody'
>       debugOldMainId = qualifyWith emptyMIdent (debugRenameId "" f)
>       debugAuxMainId = qualifyWith emptyMIdent (debugRenameId "#Aux" f)



\end{verbatim}

The first phase of the transformation process performs two diferent tasks:
\begin{itemize}
\item Transform the type of the function.
\item Change the function applications by their new names.
\end{itemize}

\begin{verbatim}

> debugFirstPhase ::  ModuleIdent -> [QualIdent] -> [Decl] ->[Decl]
> debugFirstPhase mName lExternals [] = []
> debugFirstPhase m l ((FunctionDecl ident lVars fType fExp) :xs)
>   | isQSelectorId ident = (FunctionDecl ident lVars fType fExp:xs'')
>   | otherwise           = (FunctionDecl ident lVars fType' exp':xs'')
>   where 
>     exp'   = firstPhaseExp m 0 l fExp
>     xs''   = debugFirstPhase m l xs
>     fType' = transformType (length lVars) fType

> -----------------------------------------------------------------------------
> firstPhaseExp :: ModuleIdent -> Int ->  [QualIdent] -> Expression -> Expression
>
> firstPhaseExp m d l (Function qIdent n)
>   | isQSelectorId qIdent = Function qIdent n
>   | otherwise            = firstPhaseQual m n d l qIdent True
>
> firstPhaseExp m d l (Constructor qIdent n) = firstPhaseQual m n d l qIdent False
>
> firstPhaseExp m d l (Apply e1 e2) = Apply e1' e2'
>    where
>       e1' = firstPhaseExp m (d+1) l e1
>       e2' = firstPhaseExp m 0 l e2 
>
> firstPhaseExp m d l (Case eval expr lAlts) = Case eval e1' lAlts'
>     where
>       e1'    = firstPhaseExp m 0 l expr
>       lAlts' =  foldr aux [] lAlts
>       aux (Alt term expr) xs = Alt term (firstPhaseExp m d l expr):xs

>
> firstPhaseExp m d l (Or e1 e2) = (Or e1' e2')
>    where
>       e1' = firstPhaseExp m d l e1
>       e2' = firstPhaseExp m d l e2 
>
> firstPhaseExp m d l (Exist ident e) = Exist ident e'
>    where
>       e' = firstPhaseExp m d l e
>
> firstPhaseExp m d l (Let binding e) = Let binding' e'
>    where
>       binding'= firstPhaseBinding m  0 l binding
>       e'      = firstPhaseExp m d l e
>
>
> firstPhaseExp m d l (Letrec lbind e) = Letrec lbind' e'
>    where
>       lbind'   = map  (firstPhaseBinding m 0 l) lbind
>       e'       = firstPhaseExp m d l e

> firstPhaseExp m d l input = input

> firstPhaseBinding:: ModuleIdent -> Int -> [QualIdent] -> Binding -> Binding
> firstPhaseBinding m d l (Binding ident expr) =(Binding ident expr')
>    where
>       expr' = firstPhaseExp m d l expr


> firstPhaseQual ::  ModuleIdent -> Int -> Int -> [QualIdent] -> 
>                   QualIdent -> Bool -> Expression
> firstPhaseQual m arity nArgs lExternal  qIdent isFunction =
>   if mustBeChanged then reconstructExpr isFunction qIdent' arity'
>   else reconstructExpr isFunction qIdent'' arity
>   where
>       (idModule,ident) = splitQualIdent qIdent
>       mustBeChanged =  if not isFunction  then nArgs < arity
>                             else nArgs < arity-1
>       idModule' = maybe m id idModule
>       arity'    = nArgs+1
>       ident'    = idAuxiliarFunction ident nArgs
>       ident''   = debugRenameId "" ident
>       qIdent'   = qualifyWith idModule' ident'
>       qIdent''  = if not isFunction 
>                   then qIdent 
>                   else if name ident == "try" 
>                        then debugTry
>                        else qualifyWith idModule' ident''

\end{verbatim}

Next function  gets the current module identifier, 
 a qualifier, its type, its arity {\tt n}, and a boolean value indicating
 if it is a function definded in the module, and generates 
{\tt n} new auxiliar functions in the current module.

\begin{verbatim}

> generateAuxFuncs :: ModuleIdent -> (QualIdent, (SymbolType,Int,Type)) -> [Decl]
> generateAuxFuncs m (qId,(sType,n,fType)) = 
>       if isQSelectorId qId then []
>       else if sType==IsExternal then (newexternal:auxiliary)
>       else auxiliary
>       where
>         newexternal = generateExternal m qId n fType
>         k = if  sType==IsExternal then n-2 
>             else if sType==IsFunction then n-2 
>                  else n-1
>         auxiliary = map (generateAuxFunc m (qId,(sType,k,fType))) [0..k]

> generateExternal :: ModuleIdent -> QualIdent -> Int -> Type -> Decl
> generateExternal m qId n fType = 
>       FunctionDecl qId' varsId fType' body
>       where
>       qId'             = changeFunctionqId qId
>       varsId           = map (mkIdent.("_"++).show) [0..n-1]
>       vars             = map Variable varsId
>       fType'           = transformType n  fType
>       finalApp         = createApply (Function qId n) vars
>       body             = debugBuildPairExp finalApp void


> generateAuxFunc :: ModuleIdent ->(QualIdent, (SymbolType,Int,Type)) -> Int -> Decl
> generateAuxFunc m (qId,(sType,n,fType)) i =
>       FunctionDecl qIdent' varsId fType' exp'
>       where
>       (idModule,ident) = splitQualIdent qId
>       qId'             = changeFunctionqId qId
>       ident'           = idAuxiliarFunction ident i
>       ident''          = idAuxiliarFunction ident (i+1)
>       qIdent'          = qualifyWith m ident'
>       qIdent''         = qualifyWith m ident''
>       varsId           = map (mkIdent.("_"++).show) [0..i]
>       vars             = map Variable varsId
>       fType'           = transformType (i+1)  fType
>       finalApp         = if sType==IsNewConstructor
>                          then head vars
>                          else if sType==IsConstructor
>                          then createApply (Constructor qId (i+1)) vars
>                          else createApply (Function qId' (i+2)) vars
>       nextApp          = createApply (Function qIdent'' (i+2)) vars
>       exp'             = if (i==n)
>                          then  debugBuildPairExp finalApp void
>                          else  debugBuildPairExp nextApp void

> idAuxiliarFunction :: Ident -> Int -> Ident
> idAuxiliarFunction ident n = debugRenameId ('#':show n) ident

> extractApply :: Expression -> [Expression] -> (Expression,[Expression])
> extractApply (Apply e1 e2) l = extractApply e1 (e2:l)
> extractApply e1 l =  (e1,l)

                                           
> createApply :: Expression  -> [Expression] -> Expression 
> createApply exp lExp  = foldl Apply exp lExp


> reconstructExpr :: Bool -> QualIdent -> Int-> Expression
> reconstructExpr isFunction qId n = if isFunction then (Function qId n)
>                                    else (Constructor qId n)

\end{verbatim}


Transformation of the function type. The first argument is the function arity, needed for 
the transformation.

\begin{verbatim}

> ---------------------------------------------------------------------------
> transformType :: Int ->  Type -> Type
> transformType 0  fType =  debugTypePair fType' debugTypeCTree
>     where fType' = transformType'  fType
> transformType n  (TypeArrow type1 type2) =  TypeArrow type1' type2'
>     where 
>       type1' = transformType' type1
>       type2' = transformType (n-1) type2
> transformType n  fType = transformType'  fType

> transformType' ::  Type -> Type
> transformType'  t@(TypeArrow type1 type2) = transformType (typeArity t)  t
> transformType'  (TypeConstructor ident lTypes) = 
>    TypeConstructor ident (map transformType'  lTypes)
> transformType'  (TypeVariable v) = TypeVariable v

> typeArity :: Type -> Int
> typeArity (TypeArrow _ ty) = 1 + typeArity ty
> typeArity _ = 0
> ---------------------------------------------------------------------------


\end{verbatim}

Here we collect the types  of all the data constructors and functions
defined in the program. They will be needed in order to generate the 
corresponding auxiliar functions. Also an integer is paired with the type,
representing the symbol arity, and a boolean value indicating if the symbol
is a module function.


\begin{verbatim}

> data SymbolType = IsFunction | IsConstructor | IsNewConstructor | IsExternal deriving (Eq,Show)

> type DebugTypeList = [(QualIdent,(SymbolType,Int,Type))]

> collectSymbolTypes:: [Decl] -> [Decl] -> [Decl] -> 
>                      DebugTypeList -> DebugTypeList
> collectSymbolTypes types functions externals env =
>  nub (typesPredefined functions) ++
>  ((typesFunctions functions).(typesData types).(typesExternals externals)) env


> typesFunctions,typesData,typesExternals::[Decl]-> DebugTypeList -> DebugTypeList
> typesFunctions  functions env = foldr typesFunction env functions
> typesData       types env     = foldr typesDatum env types    
        

> typesExternals  externals env = foldr typesExternal env externals


> typesFunction,typesDatum,typesExternal:: Decl ->DebugTypeList -> DebugTypeList
> typesFunction (FunctionDecl qId l ftype exp)  env  = 
>       (qId,(IsFunction,length l,ftype)):env
>
> typesDatum (DataDecl qId n l) env  = foldr (typesConst qId n)  env l
> typesDatum (NewtypeDecl newtypeId n (ConstrDecl qId lType)) env =
>       (qId,(IsNewConstructor, 1, cType)):env
>       where
>       vars = map TypeVariable [1..n]
>       cType = TypeArrow lType (TypeConstructor newtypeId vars)
>
> typesExternal (ExternalDecl qId cc s ftype) env  = 
>       (qId,(IsExternal, typeArity ftype,ftype)):env

> typesConst:: QualIdent -> Int -> ConstrDecl [Type] -> DebugTypeList -> DebugTypeList
> typesConst dataId n (ConstrDecl qId lTypes) env  = 
>       (qId,(IsConstructor, length lTypes, cType)):env
>       where
>       vars  = map TypeVariable [1..n]
>       cType = foldr TypeArrow (TypeConstructor dataId vars)  lTypes

\end{verbatim}

The transformation must add auxiliary functions for all partial applications
of the list constructor and tuple constructors which are used in the module.
These constructors are defined implicitly in every module, therefore we collect
these definitions here. Generating auxiliary functions for the list
constructor only if it used helps to avoid a name conflict when the program
is linked with an explicit goal.
\begin{verbatim}

> typesPredefined :: [Decl] -> DebugTypeList
> typesPredefined functions = nub (foldr typesBody [] functions)

> typesBody :: Decl -> DebugTypeList -> DebugTypeList
> typesBody (FunctionDecl _ _ _ e) = typesExpr e

> typesExpr :: Expression -> DebugTypeList -> DebugTypeList
> typesExpr (Literal _) env = env
> typesExpr (Variable _) env = env
> typesExpr (Function _ _) env = env
> typesExpr (Constructor qId n) env =
>   if idModule == Nothing && n > 0 then env' else env
>   where (idModule,ident) = splitQualIdent qId
>         env' = (qId,(IsConstructor,n,debugTypePredef ident n)) : env
> typesExpr (Apply e1 e2) env = typesExpr e1 (typesExpr e2 env)
> typesExpr (Case _ e alts) env = typesExpr e (foldr typesAlt env alts)
>   where typesAlt (Alt _ e) = typesExpr e
> typesExpr (Or e1 e2) env = typesExpr e1 (typesExpr e2 env)
> typesExpr (Exist _ e) env = typesExpr e env
> typesExpr (Let (Binding _ e1) e2) env = typesExpr e1 (typesExpr e2 env)
> typesExpr (Letrec binds e) env = foldr typesBinding (typesExpr e env) binds
>   where typesBinding (Binding _ e) = typesExpr e

> debugTypePredef :: Ident -> Int -> Type
> debugTypePredef ident n
>   | ident == consId && n == 2 = typeCons
>   | isTupleId ident = typeTuple n
>   | otherwise = error ("debugTypePredef: " ++ show ident ++ "/" ++ show n)

\end{verbatim}




Auxiliary functions are introduced to deal with HO parameter applications
\begin{verbatim}

> debugAuxiliary :: ModuleIdent -> [(QualIdent, (SymbolType,Int,Type))] -> [Decl]
> debugAuxiliary m xs = concat (map (generateAuxFuncs m) xs)

\end{verbatim}

The transformed rules of the original funcions. At the partial applications
of functions and constructos have been replaced by auxiliar functions. 
Also, the type of the function has been transformed.
We only need:
\begin{itemize}
\item Introduce local definition replacing function calls.
\item Guess if the function is a lifted function, in order to build an 
      appropiate name and include only the function variables in the node.
\end{itemize}

\begin{verbatim}

> ---------------------------------------------------------------------------

> debugFunction ::   Bool -> Decl -> Decl
> debugFunction trust (FunctionDecl qId lVars fType expr)
>   | isQSelectorId qId = FunctionDecl qId lVars fType expr
>   | otherwise         = FunctionDecl qId' lVars fType expr'
>   where
>     expr' = newLocalDeclarations  qId trust expr lVars (length lVars)
>     qId' = changeFunctionqId qId
        

> newLocalDeclarations :: QualIdent -> Bool -> Expression -> [Ident] ->
>                         Int -> Expression
> newLocalDeclarations qId trust exp lVars arity  = 
>       exp' 
>       where   
>         (_,exp',_) = newBindings qId exp lVars' 0 [] True trust
>         lVars'        = drop ((length lVars)-arity) lVars

\end{verbatim}

This type represent the result of the next set of functions. The first part is a
list with the new local definitions (bindings) introduced, 
the second is a list with  the new computation trees
introduced, prepared for function {\tt clean}. The last component is the
expression after the introduction of the new local definitions.

\begin{verbatim}

> type SecondPhaseResult = ([Expression],Expression,Int)

\end{verbatim}

Next functions change a expression {\tt e} into {\tt let auxN = e in } 
{\tt let resultN = fst e in } {\tt let treeN = snd e in} {\tt Variable resultN},
where $N$ represents a number used to avoid repeated name of variables.
Actually this infomation is returned in the following, more convinient format:
{\tt (Trees++[cleanTree], Variable resultId)}, where  {\tt cleanTree} is
{\tt (dVal resultN, treeN)}. The last value is the new value for $n$ that is used 
to avoid repeating identifiers.

\begin{verbatim}

> decomposeExp :: [Expression] -> Int -> Expression ->  SecondPhaseResult
>
> decomposeExp lTrees n exp = 
>       (lTrees++[cleanTree], letExp, n+1)
>       where 
>        treeId    = newIdName n "tree"
>        resultId  = newIdName n "result"
>        aux       = newIdName n "Aux"
>        auxResult = Apply (Function fst 1) (Variable aux)
>        auxTree   = Apply (Function snd 1) (Variable aux)
>        fst       = qualifyWith preludeMIdent (mkIdent "fst")
>        snd       = qualifyWith preludeMIdent (mkIdent "snd")
>        letExp    = Let (Binding aux exp) (Let (Binding resultId auxResult) 
>                    (Let (Binding treeId auxTree) (Variable resultId)) )
>        cleanTree = retrieveCleanTree (resultId,treeId)



> newBindings :: QualIdent -> Expression -> [Ident] -> Int -> 
>                 [Expression] -> Bool -> Bool -> SecondPhaseResult
> newBindings qId exp lVars n lTrees isMainExp trust = 
>       if  placeForCT then ([cleanTree], letExp,n2+1)
>       else extractBindings qId exp lVars n lTrees isMainExp trust
>       where 
>          freeCaseOr = noCaseOr exp
>          (lTrees2,exp2,n2) =  extractBindings qId exp lVars n 
>                                               lTrees False trust
>          placeForCT = isMainExp   && freeCaseOr
>          (lets,exp3)= extractLets exp2
>          treeId   = newIdName n2 "tree"
>          resultId = newIdName n2 "result"
>          vResult  = Variable resultId
>          vTree    = Variable treeId
>          cTree    = if trust then  createEmptyNode lTrees2
>                     else createTree qId lVars resultId lTrees2
>          cleanTree= retrieveCleanTree (resultId,treeId)
>          rhs      = debugBuildPairExp vResult vTree
>          bindingR = Binding resultId exp3
>          bindingT = Binding treeId cTree
>          letExp   = buildLetExp (lets++[Let bindingR,Let  bindingT]) rhs


> extractBindings :: QualIdent -> Expression -> [Ident] -> Int -> 
>                [Expression] -> Bool -> Bool -> SecondPhaseResult
>
> extractBindings qId e@(Function f a) lVars n lTrees isMainExp voidTree = 
>       if   a>0 then (lTrees,e,n)
>       else decomposeExp lTrees n e

> extractBindings qId (Case eval exp lAlt) lVars n lTrees isMainExp voidTree = 
>        ([], buildLetExp lets (Case eval e2 lAlt'),n2)
>       where
>        (lTrees1,e1,n1) = extractBindings qId exp lVars n lTrees False voidTree
>        (lets,e2) = extractLets e1
>        (lTrees2,lAlt',n2) = extractBindingsAlts qId lAlt lVars n1 lTrees1 isMainExp voidTree

> extractBindings qId (Or e1 e2) lVars n lTrees isMainExp voidTree = 
>       ([],Or e1' e2',n2)
>       where
>        (lTrees1,e1',n1) = newBindings qId e1 lVars n lTrees isMainExp voidTree
>        (lTrees2,e2',n2) = newBindings qId e2 lVars n1 lTrees isMainExp voidTree

> extractBindings qId (Exist id exp) lVars n lTrees isMainExp voidTree = 
>       (lTrees', Exist id exp',n')
>       where
>        (lTrees',exp',n') = extractBindings qId exp lVars n lTrees isMainExp voidTree

> extractBindings qId (Let binding e) lVars n lTrees isMainExp voidTree = 
>       (lTrees++lTrees2, buildLetExp lbinding' e',n2)
>       where
>        (lTrees1,lbinding',n1) = extractBindingsBinding qId binding  n  
>        (lTrees2, e',n2) = extractBindings qId e lVars n1 lTrees1 isMainExp voidTree

> extractBindings qId (Letrec lbinding e) lVars n lTrees isMainExp voidTree = 
>       (lTrees++lTrees2,buildLetrecExp lets lbinding' e',n2)
>       where
>        (lTrees1,lets,lbinding',n1) = extractBindingsLBindings qId lbinding  n
>        (lTrees2,e',n2) = extractBindings qId e lVars n1 lTrees1 isMainExp voidTree
>
> extractBindings qId e@(Apply _ _) lVars n lTrees isMainExp voidTree = 
>       (lTrees1++lTrees2, buildLetExp 
>                            ((concat (map fst letArgs2))++letse) e2,n2)
>       where
>        (f,args) = extractApply e []
>        (lTrees1,args1,n1) = extractBindingsList qId args lVars n lTrees False voidTree
>        letArgs2 = map extractLets args1
>        (lTrees2,e1,n2) = extractBindingsApply f (map snd letArgs2) n1 
>        (letse,e2) = extractLets e1
>

> extractBindings _ exp _ n lTrees _ _ = (lTrees,exp,n)


> extractBindingsApply ::  Expression -> [Expression] -> 
>                         Int ->  SecondPhaseResult

> extractBindingsApply  e@(Constructor qId arity) args  n  =
>       ([],createApply e args,n)

> extractBindingsApply f@(Function qId arity) args  n  = 
>       if length args==arity-1  then ([],partialApp,n)
>       else if isQSelectorId qId then extractBindingsApply app extraArgs n
>       else (lTrees1++lTrees2,buildLetExp lets e,n2)
>       where 
>         (nArgs,extraArgs) = splitAt arity args
>         app = createApply f nArgs
>         partialApp = createApply f args --05-12-2001
>         (lTrees1,v,n1) = decomposeExp [] n app
>         (lets,body) = extractLets v
>         (lTrees2,e,n2) = extractBindingsApply body extraArgs n1

> extractBindingsApply f []  n  = ([],f,n)
> 
> extractBindingsApply f (e:es)  n  =
>       (t++t',buildLetExp lets e',n2)
>       where 
>         app = createApply f [e]
>         (t,v,n1) = decomposeExp [] n app
>         (lets,body) = extractLets v
>         (t',e',n2) = extractBindingsApply body es n1 


> extractBindingsList::QualIdent -> [Expression] -> [Ident] -> Int -> 
>                      [Expression] -> Bool -> Bool ->
>                      ([Expression],[Expression],Int)
> extractBindingsList _ [] _ n lTrees _ _ = (lTrees,[],n)
> extractBindingsList qId (x:xs) lVars n lTrees isMainExp voidTree = 
>       (lTrees2, x':xs',n2)
>       where
>        (lTrees1,x',n1) = newBindings qId x lVars n lTrees isMainExp voidTree
>        (lTrees2,xs',n2) = extractBindingsList qId xs lVars n1 lTrees1 isMainExp voidTree 


> extractBindingsBinding:: QualIdent -> Binding ->  Int -> 
>                          ([Expression],[Expression->Expression],Int)
> extractBindingsBinding qId (Binding vId e)  n  = (lTrees,lBinding,n')
>       where
>        (lTrees,e1,n') = newBindings qId e [] n [] False False
>        (lets,e2)      = extractLets e1
>        lBinding       = lets++[Let (Binding vId e2)]


> extractBindingsLBindings:: QualIdent -> [Binding]  -> Int -> 
>                      ([Expression],[Expression->Expression],[Binding],Int)
> extractBindingsLBindings qId []  n  = ([],[],[],n)
> extractBindingsLBindings qId (x:xs)  n  = 
>       (lTrees1++lTrees2,letsX++letsXs,(Binding vId e2):xs',n2)
>       where
>        (Binding vId e) = x
>        (lTrees1,e1,n1) = newBindings qId e [] n [] False False
>        (letsX,e2)       = extractLets e1
>        (lTrees2,letsXs,xs',n2) = extractBindingsLBindings qId xs n1


> extractBindingsAlts:: QualIdent -> [Alt] -> [Ident] -> Int -> [Expression] ->
>                       Bool -> Bool -> ([Expression],[Alt],Int)

> extractBindingsAlts _ [] _ n  _ _ _    = ([],[],n)
> extractBindingsAlts qId (x:xs) lVars n lTrees isMainExp voidTree = 
>       (lTrees1++lTrees2,(Alt const e'):xs',n2)
>       where
>        (Alt const e) = x
>        (lTrees1,e',n1) = newBindings qId e lVars n lTrees isMainExp voidTree
>        (lTrees2,xs',n2) = extractBindingsAlts qId xs lVars n1 lTrees isMainExp voidTree 

          
> noCaseOr :: Expression -> Bool
> noCaseOr (Case eval expr lAlt) = False
> noCaseOr (Or exp1 exp2) = False
> noCaseOr (Apply e1 e2) = (noCaseOr e1) && (noCaseOr e2)
> noCaseOr (Exist id exp) = noCaseOr exp
> noCaseOr (Let binding exp) = (noCaseOrBinding binding) && (noCaseOr exp)
> noCaseOr (Letrec l exp) = (all noCaseOrBinding l) && (noCaseOr exp)
> noCaseOr _ = True

> noCaseOrBinding :: Binding -> Bool
> noCaseOrBinding (Binding id exp) = noCaseOr exp
          
> createTree :: QualIdent ->  [Ident] -> Ident -> [Expression] -> Expression
> createTree qId lVars resultId trees = 
>       node fName fParams fResult debugNil clean
>       where
>       (idModule,ident) = splitQualIdent qId
>       fNameCh = maybe "" moduleName idModule ++ "." ++ name ident
>       fName   = debugBuildList (map (Literal . Char) fNameCh)
>       fParams = debugBuildList (map (dEvalApply.Variable) lVars)
>       fResult = (dEvalApply.Variable) resultId
>       clean   = Apply (Function debugClean 1) (debugBuildList trees)

> buildLetExp :: [Expression->Expression] -> Expression -> Expression
> buildLetExp bindings exp =  foldr (\x y->x y) exp bindings

> buildLetrecExp :: [Expression->Expression] -> [Binding] -> Expression -> Expression
> buildLetrecExp bindings lbindings exp =
>   fixLetrecExp lbindings (buildLetExp bindings (Letrec [] exp))

> fixLetrecExp :: [Binding] -> Expression -> Expression
> fixLetrecExp lbindings (Exist var exp) = Exist var (fixLetrecExp lbindings exp)
> fixLetrecExp lbindings (Let binding exp) = fixLetrecExp (binding:lbindings) exp
> fixLetrecExp lbindings (Letrec lbindings' exp)
>   | null lbindings' = Letrec lbindings exp
>   | otherwise = fixLetrecExp (lbindings' ++ lbindings) exp

\end{verbatim}


Extract lets put all the let, exist and letrec constructions in the outer part
of the expression. Teh expression is assumed to be free of case and or expressions.

\begin{verbatim}

> outerLets :: Expression ->  Expression
> outerLets e = foldr (\x y -> x y) e' l
>       where (l,e') = extractLets e

> extractLets :: Expression ->  ([Expression->Expression],Expression)
>
> extractLets (Apply e1 e2) = (l1++l2,Apply e1'  e2')
>       where (l1,e1') = extractLets e1
>             (l2,e2') = extractLets e2
> extractLets (Exist ident e) = ((Exist ident):l1,e')
>       where (l1,e') = extractLets e
> extractLets (Let binding e) = ((Let binding):l1,e')
>       where (l1,e') = extractLets e
> extractLets (Letrec lbinding e) = ((Letrec lbinding):l1,e')
>       where (l1,e') = extractLets e
> extractLets e = ([],e)

\end{verbatim}


Function {\tt retrieveCleanTree} convert a value {\tt SecondPhaseResult} 
of the form {(res,tree),exp)} representing
a  new local let, into an element of the list of trees of the form
{\tt (dEval res,tree)}.

\begin{verbatim}

> retrieveCleanTree :: (Ident,Ident) -> Expression
> retrieveCleanTree (id1,id2) = debugBuildPairExp id1' id2'
>       where
>        id1' = dEvalApply (Variable id1 )
>        id2' = Variable id2


\end{verbatim}

\begin{verbatim}

> changeFunctionqId :: QualIdent -> QualIdent
> changeFunctionqId qId = qId'
>       where
>       (idModule,ident) = splitQualIdent qId
>       ident'    = debugRenameId "" ident
>       qId'      = maybe qId (flip qualifyWith ident') idModule

\end{verbatim}
