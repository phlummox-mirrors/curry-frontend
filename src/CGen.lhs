% -*- LaTeX -*-
% $Id: CGen.lhs,v 2.37 2004/05/01 13:18:15 wlux Exp $
%
% Copyright (c) 1998-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CGen.lhs}
\section{Generating C Code}
\begin{verbatim}

> module CGen(genMain,genEntry,genModule,genSplitModule) where
> import Cam
> import CCode
> import CPS
> import CElim
> import Char
> import List
> import Map
> import Maybe
> import Set
> import Utils

\end{verbatim}
\subsection{Start-up Code}
The functions \texttt{genMain} and \texttt{genEntry} generate the
start-up code for a Curry program. The function \texttt{genMain}
defines the main function of the program and also the global variables
that hold the default sizes of the heap, stack, and trail. The main
function initializes the runtime system by calling \verb|curry_init|,
then calls the specified function that executes the Curry program, and
finally calls \verb|curry_terminate| which eventually prints the
statistics for the run.
\begin{verbatim}

> genMain :: String -> [CTopDecl]
> genMain run = CppInclude "curry.h" : defaultVars ++ [mainFunction run]

> defaultVars :: [CTopDecl]
> defaultVars =
>   [CVarDef CPublic ty v (CInit (CExpr (defaultValue v))) | (ty,v) <- vars]
>   where vars = map ((,) sizeTy) sizes ++ map ((,) flagTy) flags
>         sizes = ["stacksize","heapsize","trailsize"]
>         sizeTy = "unsigned int"
>         flags = ["do_trace", "show_stats"]
>         flagTy = "int"
>         defaultValue v = "DEFAULT_" ++ map toUpper v

> mainFunction :: String -> CTopDecl
> mainFunction run =
>   CMainFunc "main" ["argc","argv"]
>     [CProcCall "curry_init" (map CExpr ["&argc","argv"]),
>      CLocalVar "int" "rc" (Just (funCall run ["argc","argv"])),
>      CProcCall "curry_terminate" [],
>      CProcCall "exit" [CExpr "rc"],
>      CReturn (CInt 0)]

\end{verbatim}
The function \texttt{genEntry} generates the function C function that
executes the Curry program. This is done by invoking \verb|curry_exec|
for a monadic goal and \verb|curry_eval| for a non-monadic goal,
respectively. In the latter case, the code also defines the array
holding the names of the goal's free variables.
\begin{verbatim}

> genEntry :: String -> Name -> Maybe [String] -> [CTopDecl]
> genEntry run f fvs =
>   [CMainFunc run ["argc","argv"]
>     (maybe [] (return . fvDecl "fv_names") fvs ++
>      [CReturn (curry_main fvs (infoTable f) "fv_names" ["argc","argv"])])]
>   where fvDecl v vs =
>           CStaticArray "const char *" v
>              (map CInit (map CString vs ++ [asString (CInt 0)]))
>         curry_main (Just _) = curry_eval
>         curry_main Nothing = const . curry_exec
>         curry_exec g args = funCall "curry_exec" (g:args)
>         curry_eval g v args = funCall "curry_eval" (g:v:args)

\end{verbatim}
\subsection{Modules}
The C code for a module consists of four different parts that are
partially intermixed in the generated file. The first part are
\verb|enum| declarations that associate tag numbers with every data
constructor defined or used in the module. While this is not strictly
necessary, it simplifies the code generator because it does not need
to determine the tag of a constructor when it is used. The second part
defines node info structures for the data constructors defined in the
module and provides declarations for constructors imported from other
modules. The third part defines function info tables for the functions
defined in the module and provides declarations for functions imported
from other modules. Finally, the fourth part of the code contains the
C code for the functions defined in the module.

The code generation is complicated by a few special cases that need to
be handled. In particular, the compiler must provide definitions for
those tuples that are used in the module and for the functions
\texttt{@}$_n$ that implement applications of a higher-order variable
to $n$ arguments.\footnote{Only functions with $n\geq2$ are generated.
For \texttt{@}$_1$, the function \texttt{@} is used which is
implemented in the runtime system.} These functions cannot be
predefined because there are no upper limits on the arity of a tuple
or application. As these functions may be declared in every module,
they must be declared as private -- i.e., \verb|static| -- functions.

\ToDo{The runtime system should preallocate tuple descriptors up to a
reasonable size (e.g., 10). Thus the compiler only has to create
private descriptors if a module uses a tuple with a higher arity.}

In addition, the code generator preallocates the nodes for literal
constants globally. In fact, it preallocates all constants, but this
is done independently. Constant constructors are defined together with
their node info and other constants are allocated separately for every
function because there is not much chance for them to be shared.
\begin{verbatim}

> genModule :: [Decl] -> Module -> CFile
> genModule impDs cam =
>   CppInclude "curry.h" :
>   [tagDecl t cs | DataDecl t cs <- impDs, any (`elem` usedTs) cs] ++
>   map dataDecl usedCs ++
>   [tagDecl c [ConstrDecl c n] | ConstrDecl c n <- nub (usedTts ++ usedTcs)] ++
>   concatMap (dataDef CPrivate) usedTcs ++
>   concatMap (typeDef CPublic) ds ++
>   concatMap funDecl usedFs ++
>   concat [tupleDef f (tupleArity f) | f <- usedTfs] ++
>   concat [apDef f (apArity f) | f <- apClosures] ++
>   concat [funDef f (length vs) | (f,vs,_) <- fs] ++
>   literals [c | Lit c <- ns] ++
>   apTable maxAp ++
>   concatMap tupleFunction usedTfs ++
>   concat [apFunction apClosures (apName i) | i <- [2..maxAp]] ++
>   concatMap function fs
>   where (_,ds,fs) = splitCam cam
>         (usedTts,usedTs) = partition isTupleConstr (concatMap switchTags sts)
>         usedTcs = nub (usedTcs' ++ map asConstr usedTfs)
>         (usedTcs',usedCs) = partition isTupleConstr constrs
>         (usedTfs,usedFs') =
>           partition isTuple (nub (concatMap calledFuns sts ++ closures))
>         (usedAfs,usedFs) = partition isAp usedFs'
>         maxAp = maximum (0 : [apArity f | f <- usedAfs])
>         ns = concatMap nodes sts
>         sts = map thd3 fs
>         isTupleConstr (ConstrDecl c _) = isTuple c
>         closures = nub (concatMap functions ns)
>         apClosures = filter isAp closures
>         constrs = nub [ConstrDecl c (length vs) | Constr c vs <- ns]
>         asConstr f = ConstrDecl f (tupleArity f)

> switchTags :: Stmt -> [ConstrDecl]
> switchTags (Return _) = []
> switchTags (Enter _) = []
> switchTags (Exec _ _) = []
> switchTags (Lock _ st) = switchTags st
> switchTags (Update _ _ st) = switchTags st
> switchTags (Seq _ st1 st2) = switchTags st1 ++ switchTags st2
> switchTags (Let _ st) = switchTags st
> switchTags (Switch _ _ cases) = concatMap altTags cases
>   where altTags (Case t st) = patternTags t ++ switchTags st
>         patternTags (LitCase _) = []
>         patternTags (ConstrCase c vs) = [ConstrDecl c (length vs)]
>         patternTags DefaultCase = []
> switchTags (Choices alts) = concatMap switchTags alts

> nodes :: Stmt -> [Expr]
> nodes (Return _) = []
> nodes (Enter _) = []
> nodes (Exec _ _) = []
> nodes (Lock _ st) = nodes st
> nodes (Update _ _ st) = nodes st
> nodes (Seq _ st1 st2) = nodes st1 ++ nodes st2
> nodes (Let bds st) = [n | Bind _ n <- bds] ++ nodes st
> nodes (Switch Rigid _ cases) = concat [nodes st | Case _ st <- cases]
> nodes (Switch Flex _ cases) =
>   concat [freshNodes t ++ nodes st | Case t st <- cases]
>   where freshNodes t = [n | ds <- fresh undefined t, Bind _ n <- ds]
> nodes (Choices alts) = concat [nodes st | st <- alts]

> functions :: Expr -> [Name]
> functions (Lit _) = []
> functions (Constr _ _) = []
> functions (Closure f _) = [f]
> functions (Lazy f _) = [f]
> functions Free = []
> functions (Ref _) = []

> calledFuns :: Stmt -> [Name]
> calledFuns (Return _) = []
> calledFuns (Enter _) = []
> calledFuns (Exec f _) = [f]
> calledFuns (Lock _ st) = calledFuns st
> calledFuns (Update _ _ st) = calledFuns st
> calledFuns (Seq _ st1 st2) = calledFuns st1 ++ calledFuns st2
> calledFuns (Let _ st) = calledFuns st
> calledFuns (Switch _ _ cases) = concat [calledFuns st | Case _ st <- cases]
> calledFuns (Choices alts) = concatMap calledFuns alts

\end{verbatim}
The function \texttt{genSplitModule} generates separate C files for
each data type -- except abstract types, i.e., data types with an
empty data constructor list -- and function defined in a module. This
is used to build archive files for the standard library.
\begin{verbatim}

> genSplitModule :: [Decl] -> Module -> [CFile]
> genSplitModule impDs cam =
>   [genModule ms' [DataDecl t cs] | DataDecl t cs <- ds', not (null cs)] ++
>   [genModule (impDs ++ ds') [FunctionDecl f vs st] | (f,vs,st) <- fs]
>   where (ms,ds,fs) = splitCam cam
>         ms' = map ImportDecl ms
>         ds' = map (uncurry DataDecl) ds

\end{verbatim}
\subsection{Data Types and Constants}
For every data type, the compiler defines an enumeration which assigns
tag numbers to its data constructors and it also defines node info
structures for every data constructor. Furthermore, constant
constructors and literal constants are preallocated here. Note that
character constants are allocated in a table defined by the runtime
system. Integer constants need to be allocated only if the boxed
representation is used, otherwise they are encoded in the node
pointers.
\begin{verbatim}

> tagDecl :: Name -> [ConstrDecl] -> CTopDecl
> tagDecl _ cs =
>   CEnumDecl [CConst (dataTag c) (Just n)
>             | (ConstrDecl c _,n) <- zip cs [0..], c /= Name "_"]

> dataDecl :: ConstrDecl -> CTopDecl
> dataDecl (ConstrDecl c n)
>   | n == 0 = CExternVarDecl "NodeInfo *" (constNode c)
>   | otherwise = CExternVarDecl "NodeInfo" (dataInfo c)

> typeDef :: CVisibility -> (Name,[ConstrDecl]) -> [CTopDecl]
> typeDef vb (t,cs) = tagDecl t cs : concatMap (dataDef vb) cs

> dataDef :: CVisibility -> ConstrDecl -> [CTopDecl]
> dataDef vb (ConstrDecl c n)
>   | n == 0 =
>       [CVarDef CPrivate "NodeInfo" (dataInfo c) nodeinfo,
>        CVarDef vb "NodeInfo *" (constNode c)
>                (CInit (CAddr (CExpr (dataInfo c))))]
>   | otherwise = [CVarDef vb "NodeInfo" (dataInfo c) nodeinfo]
>   where nodeinfo = CStruct (map CInit nodeinfo')
>         nodeinfo' =
>           [CExpr (dataTag c),CFunCall "constr_node_size" [CInt n],
>            gcPointerTable,CExpr "eval_whnf",CString name,notFinalized]
>         name = snd $ splitQualified $ demangle c

> literals :: [Literal] -> [CTopDecl]
> literals cs =
>   CppCondDecls "ONLY_BOXED_OBJECTS"
>                (map intConstant (nub [i | Int i <- cs])) :
>   map floatConstant (nub [f | Float f <- cs])

> intConstant :: Int -> CTopDecl
> intConstant i =
>   CVarDef CPrivate "struct int_node" (constInt i)
>           (CStruct $ map CInit [CAddr (CExpr "int_info"),CInt i])

> floatConstant :: Double -> CTopDecl
> floatConstant f =
>   CVarDef CPrivate "struct float_node" (constFloat f)
>           (CStruct $ map CInit [CAddr (CExpr "float_info"),CFloat f])

> gcPointerTable, notFinalized :: CExpr
> gcPointerTable = CExpr "(const int *)0"
> notFinalized = CExpr "(FinalFun)0"

\end{verbatim}
\subsection{Functions}
Besides the code for every function, the compiler must also define
function info vectors for them. These info vectors are used to
construct closure nodes for (partial) function applications. As a
special case, the node info structures for the functions
\texttt{@}$_n$ are allocated in a single vector because these
functions are never applied partially.
\begin{verbatim}

> entryDecl :: CVisibility -> Name -> CTopDecl
> entryDecl vb f = CFuncDecl vb (cName f)

> evalDecl :: Name -> CTopDecl
> evalDecl f = CFuncDecl CPrivate (evalFunc f)

> lazyDecl :: Name -> CTopDecl
> lazyDecl f = CFuncDecl CPrivate (lazyFunc f)

> funDecl :: Name -> [CTopDecl]
> funDecl f =
>   [entryDecl CPublic f,
>    CExternArrayDecl "FunctionInfo" (infoTable f),
>    CExternVarDecl "NodeInfo" (lazyInfo f),
>    CExternVarDecl "struct closure_node" (constFunc f)]

> funDef :: Name -> Int -> [CTopDecl]
> funDef f n = closDef CPublic f n ++ lazyDef CPublic f

> tupleDef :: Name -> Int -> [CTopDecl]
> tupleDef f n = closDef CPrivate f n

> closDef :: CVisibility -> Name -> Int -> [CTopDecl]
> closDef vb f n =
>   [entryDecl vb f,evalDecl f,
>    CArrayDef vb "FunctionInfo" (infoTable f) [funInfo f i n | i <- [0..n]],
>    CVarDef vb "struct closure_node" (constFunc f)
>            (CStruct [CInit (CExpr (infoTable f)),
>                      CStruct [CInit (asNode (CInt 0))]])]

> lazyDef :: CVisibility -> Name -> [CTopDecl]
> lazyDef vb f =
>   [lazyDecl f,
>    CVarDef vb "NodeInfo" (lazyInfo f) (CStruct (map CInit (suspinfo f)))]
>   where suspinfo f =
>           [CExpr "SUSPEND_TAG",CExpr "suspend_node_size",gcPointerTable,
>            CExpr (lazyFunc f),CExpr "(const char *)0",notFinalized]

> funInfo :: Name -> Int -> Int -> CInitializer
> funInfo f i n = CStruct (funinfo f i n)
>   where funinfo f i n =
>           [CStruct (map CInit (nodeinfo f i n)),
>            CInit (CExpr (cName f)),CInit (CInt n)]
>         nodeinfo f i n =
>           [CExpr (if i < n then "PAPP_TAG" else "CLOSURE_TAG"),
>            CFunCall "closure_node_size" [CInt i],gcPointerTable,
>            CExpr (if i < n then "eval_whnf" else evalFunc f),
>            CString (undecorate (demangle f)),notFinalized]

> apDef :: Name -> Int -> [CTopDecl]
> apDef f n
>   | n >= 2 =
>       [entryDecl CPrivate f,evalDecl f,
>        CVarDef CPrivate "FunctionInfo" (dataInfo f) (apInfo f (n+1))] ++
>       lazyDef CPrivate f
>   | otherwise = []
>   where apInfo f n = funInfo f n n

> apTable :: Int -> [CTopDecl]
> apTable n
>   | n >= 2 =
>       map (entryDecl CPrivate) [apName i | i <- [2..n]] ++
>       [CArrayDef CPrivate "Label" applyTable
>                  [CInit (CExpr (cName (apName i))) | i <- [1..n-1]]]
>   | otherwise = []

\end{verbatim}
\subsection{Code Generation}
The compiler transforms each abstract machine code function into a
list of continuation passing style functions, and translates all of
these functions into distinct C functions. In addition, the compiler
generates the evaluation code for the fully applied closure node and
the suspend node associated with the abstract machine code function.
\begin{verbatim}

> function :: (Name,[Name],Stmt) -> [CTopDecl]
> function (f,vs,st) =
>   evalFunction f n : lazyFunction f n : cFunction CPublic f vs st
>   where n = length vs

> cFunction :: CVisibility -> Name -> [Name] -> Stmt -> [CTopDecl]
> cFunction vb f vs st = funcDefs vb f vs (cpsFunction f vs st)

> evalFunction :: Name -> Int -> CTopDecl
> evalFunction f n = CFuncDef CPrivate (evalFunc f) (evalCode f n)
>   where evalCode f n =
>           [CProcCall "CHECK_STACK" [CInt (n - 1)] | n > 1] ++
>           CLocalVar "Node *" "clos" (Just (CExpr "sp[0]")) :
>           [CDecrBy (LVar "sp") (CInt (n - 1)) | n /= 1] ++
>           [saveArg i | i <- [0..n-1]] ++ [goto (cName f)]
>         saveArg i = CAssign (LElem (LVar "sp") (CInt i))
>                             (CElem (CExpr "clos->cl.args") (CInt i))

> lazyFunction :: Name -> Int -> CTopDecl
> lazyFunction f n = CFuncDef CPrivate (lazyFunc f) (lazyCode f n)
>   where lazyCode f n =
>           CLocalVar "Node *" "susp" (Just (CExpr "sp[0]")) :
>           CIf (CFunCall "!is_local_space" [field "susp" "s.spc"])
>               [tailCall "suspend_thread" ["resume","susp"]]
>               [] :
>           CProcCall "CHECK_STACK" [CInt (n + 1)] :
>           CDecrBy (LVar "sp") (CInt (n + 1)) :
>           CLocalVar "Node *" "clos" (Just (field "susp" "s.fn")) :
>           CProcCall "SAVE" (map CExpr ["susp","q.wq"]) :
>           [saveArg "clos->cl.args" i | i <- [0..n-1]] ++
>           [CAssign (LElem (LVar "sp") (CInt n)) (CExpr "(Node *)update"),
>            CAssign (LVar "susp->info") (CAddr (CExpr "queueMe_info")),
>            CAssign (LVar "susp->q.wq") (CExpr "(ThreadQueue)0"),
>            goto (cName f)]
>         saveArg args i = CAssign (LElem (LVar "sp") (CInt i))
>                                  (CElem (CExpr args) (CInt i))

> tupleFunction :: Name -> [CTopDecl]
> tupleFunction f = evalFunction f n : cFunction CPrivate f vs (tuple v vs)
>   where n = tupleArity f
>         (v:vs) = [Name ('v' : show i) | i <- [0..n]]
>         tuple v vs = Let [Bind v (Constr f vs)] (Return v)

> apFunction :: [Name] -> Name -> [CTopDecl]
> apFunction apClosures f
>   | n >= 2 = closDefs f (n + 1) ++ funcDefs CPrivate f vs (cpsApply f vs)
>   | otherwise = []
>   where n = apArity f
>         vs = [Name ('v' : show i) | i <- [0..n]]
>         closDefs f n
>           | f `elem` apClosures = [evalFunction f n,lazyFunction f n]
>           | otherwise = []

> funcDefs :: CVisibility -> Name -> [Name] -> [CPSFunction] -> [CTopDecl]
> funcDefs vb f vs (k:ks) =
>   map privFuncDecl ks ++ concatMap cArrays (k:ks) ++
>   entryDef vb f vs k : map funcDef ks

> privFuncDecl :: CPSFunction -> CTopDecl
> privFuncDecl k = topDecl k (CFuncDecl CPrivate (cpsName k))

> entryDef :: CVisibility -> Name -> [Name] -> CPSFunction -> CTopDecl
> entryDef vb f vs k
>   | vs == cpsVars k = topDecl k (CFuncDef vb (cpsName k)
>                                    (entryCode f (length vs) : funCode k))
>   | otherwise = error ("internal error: entryDef " ++ demangle f)

> funcDef :: CPSFunction -> CTopDecl
> funcDef k = topDecl k (CFuncDef CPrivate (cpsName k) (funCode k))

> topDecl :: CPSFunction -> CTopDecl -> CTopDecl
> topDecl (CPSFunction _ _ c _ _ _) d = maybe d (flip CppCondDecls [d]) c

> entryCode :: Name -> Int -> CStmt
> entryCode f n =
>   CTrace "%I enter %s%V\n"
>          [CString (undecorate (demangle f)),CInt n,CExpr "sp"]

\end{verbatim}
For each \texttt{choices} statement, the compiler generates a global
array containing the entry-points of its continuations. Note that each
array is used in two functions when stability is enabled (cf.
\texttt{cpsChoose} in Sect.~\ref{sec:cps}).
\begin{verbatim}

> cArrays :: CPSFunction -> [CTopDecl]
> cArrays k@(CPSFunction f _ c _ _ st) = maybe (cArraysStmt st) (const []) c
>   where cArraysStmt (CPSYield _ st _) = cArraysStmt st
>         cArraysStmt (CPSSwitch _ _ vcase cases) =
>           maybe [] cArraysStmt vcase ++
>           concatMap (cArrays . fromCaseBlock f) cases
>         cArraysStmt (CPSLocalSwitch _ st cb) =
>           cArraysStmt st ++ cArrays (fromCaseBlock f cb)
>         cArraysStmt (CPSChoices ks) = [choicesArrayDecl ks]
>         cArraysStmt _ = []

> choicesArrayDecl :: ChoicesList -> CTopDecl
> choicesArrayDecl ks@(ChoicesList _ _ ks') =
>   CArrayDef CPrivate "Label" (choicesArray ks)
>     (map (CInit . CExpr . cpsName) ks' ++ [CInit (CExpr "(Label)0")])

\end{verbatim}
The compiler generates a C function from every CPS function. At the
beginning of a function, stack and heap checks are performed if
necessary. After the heap check, the function's arguments are loaded
from the stack. When generating the code for a case in a
\texttt{switch} statement, we try to share these variables.
However, if the code in the case performs a heap check, the variables
have to be reloaded from the stack because the garbage collector does
not trace local variables. Note that the code generated by
\texttt{caseCode} is enclosed in a \texttt{CBlock} so that the
declarations generated by \texttt{loadVars} are not moved to a place
where they might inadvertently shadow the variables loaded at the
beginning of the function.

When saving arguments to the stack, we avoid to save variables that
were loaded from the same offset in the stack because the optimizer of
the Gnu C compiler does not detect such redundant save operations.
\begin{verbatim}

> funCode :: CPSFunction -> [CStmt]
> funCode (CPSFunction _ _ _ vs dss st) =
>   elimUnused (stackCheck vs st ++ heapCheck consts dss ++ loadVars vs ++
>               allocCode consts dss ++ cCode vs st)
>   where consts = constants dss

> caseCode :: Name -> CaseBlock -> [CStmt]
> caseCode v (CaseBlock _ t vs dss st) =
>   [CBlock (stackCheck vs st ++ heapCheck' dss vs ++ fetchArgs v t ++
>            allocCode consts dss ++ cCode vs st)]
>   where consts = constants dss
>         heapCheck' dss vs
>           | all (isConstant consts) [v | ds <- dss, Bind v _ <- ds] = []
>           | otherwise = heapCheck consts dss ++ loadVars vs

> loadVars :: [Name] -> [CStmt]
> loadVars vs = zipWith loadVar vs [0..]
>   where loadVar v i =
>           CLocalVar "Node *" (show v) (Just (CElem (CExpr "sp") (CInt i)))

> fetchArgs :: Name -> Tag -> [CStmt]
> fetchArgs v (LitCase _) = []
> fetchArgs v (ConstrCase _ vs) =
>   assertRel (funCall "constr_argc" [show v]) "==" (CInt (length vs)) :
>   zipWith (fetchArg (field (show v) "c.args")) vs [0..]
>   where fetchArg v v' = CLocalVar "Node *" (show v') . Just . CElem v . CInt
> fetchArgs v DefaultCase = []

> saveVars :: [Name] -> [Name] -> [CStmt]
> saveVars vs0 vs =
>   [CIncrBy (LVar "sp") (CInt d) | d /= 0] ++
>   [saveVar i v | (i,v0,v) <- zip3 [0..] vs0' vs, v0 /= v]
>   where d = length vs0 - length vs
>         vs0' = if d >= 0 then drop d vs0 else replicate (-d) (Name "") ++ vs0
>         saveVar i v = CAssign (LElem (LVar "sp") (CInt i)) (CExpr (show v))

> updVar :: [Name] -> Name -> CStmt
> updVar vs v
>   | null vs'' = error ("updVar " ++ show v)
>   | otherwise =
>       CAssign (LElem (LVar "sp") (CInt (length vs'))) (CExpr (show v))
>   where (vs',vs'') = break (v ==) vs

\end{verbatim}
For every function we have to compute its stack and heap requirements.
\begin{verbatim}

> heapCheck :: FM Name CExpr -> [[Bind]] -> [CStmt]
> heapCheck consts dss = [CProcCall "CHECK_HEAP" [n] | n /= CInt 0]
>   where n = foldr add (CInt 0)
>                   [nodeSize n | ds <- dss, Bind v n <- ds,
>                                 not (isConstant consts v)]
 
> nodeSize :: Expr -> CExpr
> nodeSize (Lit c) = litNodeSize c
> nodeSize (Constr _ vs) = CFunCall "constr_node_size" [CInt (length vs)]
> nodeSize (Closure _ vs) = CFunCall "closure_node_size" [CInt (length vs)]
> nodeSize (Lazy f vs) =
>   CExpr "suspend_node_size" `CAdd` nodeSize (Closure f vs)
> nodeSize Free = CExpr "variable_node_size"
> nodeSize (Ref _) = error "internal error: nodeSize(Ref)"

> litNodeSize :: Literal -> CExpr
> litNodeSize (Char _) = CExpr "char_node_size"
> litNodeSize (Int _) = CExpr "int_node_size"
> litNodeSize (Float _) = CExpr "float_node_size"

\end{verbatim}
The maximum stack depth of a function is simply the difference of the
number of arguments passed to the function and the number of arguments
pushed onto the stack when calling the continuation. Note that
\texttt{CPSEnter} may push the node to be evaluated onto the stack. No
stack check is performed before a \texttt{CPSApply} statement because
the required stack depth depends on the number of arguments saved in
the closure that is applied. In the case of a \texttt{CPSSwitch}
statement, every alternative is responsible for performing a stack
check.
\begin{verbatim}

> stackCheck :: [Name] -> CPSStmt -> [CStmt]
> stackCheck vs st = [CProcCall "CHECK_STACK" [CInt depth] | depth > 0]
>   where depth = stackDepth st - length vs

> stackDepth :: CPSStmt -> Int
> stackDepth (CPSJump k) = length (cpsVars k)
> stackDepth (CPSReturn _ k) = 0 + stackDepthCont k
> stackDepth (CPSEnter _ k) = 1 + stackDepthCont k
> stackDepth (CPSExec _ vs k) = length vs + stackDepthCont k
> stackDepth (CPSLock _ st) = stackDepth st
> stackDepth (CPSUpdate _ _ st) = stackDepth st
> stackDepth (CPSApply _ _) = 0
> stackDepth (CPSBind _ _ k) = length (cpsVars k)
> stackDepth (CPSDelay _ k) = length (cpsVars k)
> stackDepth (CPSYield _ st k) = max (stackDepth st) (length (cpsVars k))
> stackDepth (CPSSwitch _ _ _ _) = 0
> stackDepth (CPSLocalSwitch _ st _) = stackDepth st
> stackDepth (CPSChoices (ChoicesList _ _ (k:_))) = length (cpsVars k)

> stackDepthCont :: Maybe CPSFunction -> Int
> stackDepthCont = maybe 0 (length . cpsVars)

\end{verbatim}
All constants that are used in a function are preallocated in a static
array \texttt{Node *constants[]} at the beginning of that function.
The following functions compute the set of variables which are bound
to constants together with their respective initializer expressions.
Recall that literals as well as nullary data constructors and partial
applications without arguments are allocated globally in order to
improve sharing.

In order to detect constants in recursive data definitions like
\verb|let { xs=0:ys; ys=1:xs } in |\dots{} efficiently, the
declarations in a let statement were split into minimal binding groups
when the code was transformed into CPS. In addition, we separate the
computation of the list of variables from the association of
initializer expressions.
\begin{verbatim}

> isConstant :: FM Name CExpr -> Name -> Bool
> isConstant consts v = isJust (lookupFM v consts)

> constants :: [[Bind]] -> FM Name CExpr
> constants dss = fromListFM $ snd $
>   mapAccumL init 0 [(v,n) | ds <- dss, Bind v n <- ds, v `elemSet` vs0]
>   where vs0 = constVars dss
>         init o (v,Lit c) = (o,(v,literal c))
>         init o (v,Constr c vs)
>           | null vs = (o,(v,constRef (constNode c)))
>           | otherwise = (o + length vs + 1,(v,constant o))
>         init o (v,Closure f vs)
>           | null vs = (o,(v,constRef (constFunc f)))
>           | otherwise = (o + length vs + 1,(v,constant o))
>         init o (v,Ref v') = (o,(v,CExpr (show v')))
>         init _ (v,n) = error ("internal error: constants.init" ++ show n)
>         constant = asNode . add (CExpr constArray) . CInt

> constVars :: [[Bind]] -> Set Name
> constVars = foldl_strict addConst zeroSet
>   where addConst vs0 ds = if all (isConst vs0') ns then vs0' else vs0
>           where vs0' = foldr addToSet vs0 vs
>                 (vs,ns) = unzip [(v,n) | Bind v n <- ds]
>         isConst _ (Lit _) = True
>         isConst vs0 (Constr _ vs) = all (`elemSet` vs0) vs
>         isConst vs0 (Closure _ vs) = all (`elemSet` vs0) vs
>         isConst _ (Lazy _ _) = False
>         isConst _ Free = False
>         isConst vs0 (Ref v) = v `elemSet` vs0

> literal :: Literal -> CExpr
> literal (Char c) = asNode (CAdd (CExpr "char_table") (CInt (ord c)))
> literal (Int i) =
>   CFunCall "IF_UNBOXED" [CFunCall "mk_int" [CInt i],constRef (constInt i)]
> literal (Float f) = constRef (constFloat f)

> allocCode :: FM Name CExpr -> [[Bind]] -> [CStmt]
> allocCode consts dss =
>   [CStaticArray "Node *" constArray is | not (null is)] ++
>   concatMap (allocNode consts) ds ++ concatMap (initNode consts) ds
>   where is = constData consts ds
>         ds = concat dss

> constData :: FM Name CExpr -> [Bind] -> [CInitializer]
> constData consts ds = map (CInit . asNode) $ foldr constInit [] ds
>   where constInit (Bind v (Constr c vs)) is
>           | not (null vs) && isConstant consts v =
>               CAddr (CExpr (dataInfo c)) : map arg vs ++ is
>         constInit (Bind v (Closure f vs)) is
>           | not (null vs) && isConstant consts v =
>               functionInfo f (length vs) : map arg vs ++ is
>         constInit _ is = is
>         arg v = fromJust (lookupFM v consts)

\end{verbatim}
The compiler creates two nodes for lazy applications. The first is a
non-lazy closure node for the application, and the second is a suspend
node which is going to be overwritten with an indirection once the
application has been evaluated. This layout is used because it is
better suited for recording updates on the trail. Otherwise, the
runtime system would have to overwrite and save \emph{all} arguments
of a lazy application node when its evaluation is started.
\begin{verbatim}

> allocNode :: FM Name CExpr -> Bind -> [CStmt]
> allocNode consts (Bind v n) =
>   case lookupFM v consts of
>     Just e -> [CLocalVar "Node *" v' (Just e)]
>     Nothing ->
>       case n of
>         Lit c -> [CLocalVar "Node *" v' (Just (literal c))]
>         Ref v'' -> [CLocalVar "Node *" v' (Just (CExpr (show v'')))]
>         Lazy f vs ->
>           [CLocalVar "Node *" (closVar v) (Just (asNode (CExpr "hp"))),
>            CLocalVar "Node *" v'
>              (Just (asNode (CExpr "hp" `CAdd` nodeSize (Closure f vs)))),
>            CIncrBy (LVar "hp") (nodeSize n)]
>         _ -> [CLocalVar "Node *" v' (Just (asNode (CExpr "hp"))),
>               CIncrBy (LVar "hp") (nodeSize n)]
>   where v' = show v

> initNode :: FM Name CExpr -> Bind -> [CStmt]
> initNode _ (Bind v (Lit _)) = []
> initNode consts (Bind v (Constr c vs))
>   | isConstant consts v = []
>   | otherwise = initConstr (LVar (show v)) c (map show vs)
> initNode consts (Bind v (Closure f vs))
>   | isConstant consts v = []
>   | otherwise = initClosure (LVar (show v)) f (map show vs)
> initNode _ (Bind v (Lazy f vs)) =
>   initClosure (LVar v') f (map show vs) ++ initSusp (LVar (show v)) f v'
>   where v' = closVar v
> initNode _ (Bind v Free) = initFree (LVar (show v))
> initNode _ (Bind v (Ref _)) = []

> initConstr :: LVar -> Name -> [String] -> [CStmt]
> initConstr v c vs =
>   CAssign (LField v "info") (CAddr (CExpr (dataInfo c))) :
>   initArgs (LField v "c.args") vs

> initClosure :: LVar -> Name -> [String] -> [CStmt]
> initClosure v f vs =
>   CAssign (LField v "cl.info") (functionInfo f (length vs)) :
>   initArgs (LField v "cl.args") vs

> initSusp :: LVar -> Name -> String ->[CStmt]
> initSusp v f v' =
>   [CAssign (LField v "info") (CAddr (CExpr (lazyInfo f))),
>    CAssign (LField v "s.fn") (CExpr v'),
>    CAssign (LField v "s.spc") (CExpr "ss")]

> initFree :: LVar -> [CStmt]
> initFree v =
>   [CAssign (LField v "info") (CAddr (CExpr "variable_info")),
>    CAssign (LField v "v.cstrs") (CExpr "(Constraint *)0"),
>    CAssign (LField v "v.wq") (CExpr "(ThreadQueue)0"),
>    CAssign (LField v "v.spc") (CExpr "ss")]

> initArgs :: LVar -> [String] -> [CStmt]
> initArgs v vs = zipWith (initArg v) [0..] vs
>   where initArg v i = CAssign (LElem v (CInt i)) . CExpr

\end{verbatim}
Every abstract machine statement is translated by its own
translation function.
\begin{verbatim}

> cCode :: [Name] -> CPSStmt -> [CStmt]
> cCode vs0 (CPSJump k) = jump vs0 k
> cCode vs0 (CPSReturn v k) = ret vs0 v k
> cCode vs0 (CPSEnter v k) = enter vs0 v k
> cCode vs0 (CPSExec f vs k) = exec vs0 f vs k
> cCode vs0 (CPSLock v st) = lock vs0 v st
> cCode vs0 (CPSUpdate v1 v2 st) = update vs0 v1 v2 st
> cCode vs0 (CPSApply v vs) = apply vs0 v vs
> cCode vs0 (CPSBind v v' k) = bind vs0 v v' k
> cCode vs0 (CPSDelay v k) = delay vs0 v k
> cCode vs0 (CPSYield v st k) = yield vs0 v st k
> cCode vs0 (CPSSwitch unboxed v vcase cases) =
>   switchOnTerm unboxed vs0 v (maybe [CBreak] (cCode vs0) vcase)
>                [(caseBlockTag cb,caseCode v cb) | cb <- cases]
> cCode vs0 (CPSLocalSwitch v st cb) = localSwitch vs0 v st cb
> cCode vs0 (CPSChoices ks) = choices vs0 ks

> jump :: [Name] -> CPSFunction -> [CStmt]
> jump vs0 k = saveVars vs0 (cpsVars k) ++ [goto (cpsName k)]

> ret :: [Name] -> Name -> Maybe CPSFunction -> [CStmt]
> ret vs0 v Nothing =
>   saveVars vs0 [] ++
>   [CLocalVar "Label" "ret_ip" (Just (asLabel (CExpr "sp[0]"))),
>    CAssign (LVar "sp[0]") result,
>    CTrace "%I return %N\n" [result],
>    goto "ret_ip"]
>   where result = CExpr (show v)
> ret vs0 v (Just k) =
>   saveVars vs0 (v : tail (cpsVars k)) ++ [goto (cpsName k)]

> enter :: [Name] -> Name -> Maybe CPSFunction -> [CStmt]
> enter vs0 v k =
>   CLocalVar "Node *" v' (Just (CExpr (show v))) :
>   tagSwitch (Name v') [] (Just [])
>             [CCase "CLOSURE_TAG" [{- fall through! -}],
>              CCase "SUSPEND_TAG" [{- fall through! -}],
>              CCase "QUEUEME_TAG"
>                    (saveCont vs0 [Name v'] k ++
>                     [gotoExpr (field v' "info->eval")])] :
>   ret vs0 (Name v') k
>   where v' = "_node"

> exec :: [Name] -> Name -> [Name] -> Maybe CPSFunction -> [CStmt]
> exec vs0 f vs k = saveCont vs0 vs k ++ [goto (cName f)]

> lock :: [Name] -> Name -> CPSStmt -> [CStmt]
> lock vs0 v st =
>   rtsAssertList[isBoxed v',CRel (nodeTag v') "==" (CExpr "SUSPEND_TAG"),
>                 CFunCall "is_local_space" [field (show v') "s.spc"]] :
>   CProcCall "SAVE" (map CExpr [v',"q.wq"]) :
>   CAssign (LField (LVar v') "info") (CAddr (CExpr "queueMe_info")) :
>   CAssign (LField (LVar v') "q.wq") (CExpr "(ThreadQueue)0") :
>   cCode vs0 st
>   where v' = show v

> update :: [Name] -> Name -> Name -> CPSStmt -> [CStmt]
> update vs0 v1 v2 st =
>   rtsAssertList[isBoxed v1',CRel (nodeTag v1') "==" (CExpr "QUEUEME_TAG"),
>                 CFunCall "is_local_space" [field (show v1') "q.spc"]] :
>   CLocalVar "ThreadQueue" wq (Just (CField (CExpr v1') "q.wq")) :
>   CProcCall "SAVE" (map CExpr [v1',"q.wq"]) :
>   CAssign (LField (LVar v1') "info") (CAddr (CExpr "suspend_indir_info")) :
>   CAssign (LField (LVar v1') "n.node") (CExpr (show v2)) :
>   CIf (CRel (CExpr wq) "!=" (CExpr "(ThreadQueue)0"))
>       [CProcCall "wake_threads" [CExpr wq]]
>       [] :
>   cCode vs0 st
>   where v1' = show v1
>         wq = "wq"

> saveCont :: [Name] -> [Name] -> Maybe CPSFunction -> [CStmt]
> saveCont vs0 vs Nothing = saveVars vs0 vs
> saveCont vs0 vs (Just k) =
>   CLocalVar "Node *" ip (Just (asNode (CExpr (cpsName k)))) :
>   saveVars vs0 (vs ++ Name ip : tail (cpsVars k))
>   where ip = "cont_ip"

> bind :: [Name] -> Name -> Name -> CPSFunction -> [CStmt]
> bind vs0 v n k =
>   saveVars vs0 [if v == v' then n else v' | v' <- cpsVars k] ++
>   [tailCall "bind_var" [show v,show n,cpsName k]]

> delay :: [Name] -> Name -> CPSFunction -> [CStmt]
> delay vs0 v k =
>   saveVars vs0 (cpsVars k) ++ [tailCall "delay_thread" [cpsName k,show v]]

> yield :: [Name] -> Maybe Name -> CPSStmt -> CPSFunction -> [CStmt]
> yield vs0 v st k =
>   CppCondStmts "YIELD_NONDET"
>     [CIf (CExpr "rq != (ThreadQueue)0")
>          (saveVars vs0 (cpsVars k) ++ [yieldCall (cpsName k) v])
>          []]
>     [] :
>   cCode vs0 st
>   where yieldCall k (Just v) = tailCall "yield_delay_thread" [k,show v]
>         yieldCall k Nothing = tailCall "yield_thread" [k]

> localSwitch :: [Name] -> Name -> CPSStmt -> CaseBlock -> [CStmt]
> localSwitch vs0 v st cb =
>   CIf (CFunCall "!is_local_space" [field (show v) "v.spc"])
>       (cCode vs0 st)
>       [] :
>   caseCode v cb

> choices :: [Name] -> ChoicesList -> [CStmt]
> choices vs0 ks@(ChoicesList _ _ (k:_)) =
>   saveVars vs0 (cpsVars k) ++
>   [CAssign (LVar "choice_conts") (CExpr (choicesArray ks)),
>    goto "nondet_handlers.choices"]

> failAndBacktrack :: [CStmt]
> failAndBacktrack = [goto "nondet_handlers.fail"]

\end{verbatim}
Code generation for a \texttt{CPSSwitch} statement is a little bit
complex because matching literal constants requires two nested
switches. The outer switch matches for the common tag, whereas the
inner switch matches the literal's value. Furthermore, integer
literals are encoded in the pointer instead of using a node in the
heap when the preprocessor constant \texttt{ONLY\_BOXED\_OBJECTS} is
\texttt{0}, which is the default configuration.
\begin{verbatim}

> switchOnTerm :: Bool -> [Name] -> Name -> [CStmt] -> [(Tag,[CStmt])]
>              -> [CStmt]
> switchOnTerm maybeUnboxed vs0 v varCode cases =
>   tagSwitch v [updVar vs0 v] unboxedCase otherCases :
>   head (dflts ++ [failAndBacktrack])
>   where (lits,constrs,dflts) = foldr partition ([],[],[]) cases
>         (chars,ints,floats) = foldr litPartition ([],[],[]) lits
>         unboxedCase
>           | maybeUnboxed =
>               Just [CppCondStmts "!ONLY_BOXED_OBJECTS" [intSwitch v ints] []
>                    | not (null ints)]
>           | otherwise = Nothing
>         otherCases =
>           varCase : [charCase | not (null chars)] ++
>           [intCase | not (null ints)] ++ [floatCase | not (null floats)] ++
>           map constrCase constrs
>         varCase = CCase "VARIABLE_TAG" varCode
>         charCase = CCase "CHAR_TAG" [charSwitch v chars,CBreak]
>         intCase = CCase "INT_TAG"
>                     [CppCondStmts "ONLY_BOXED_OBJECTS" [intSwitch v ints] [],
>                      CBreak]
>         floatCase = CCase "FLOAT_TAG" (floatSwitch v floats ++ [CBreak])
>         constrCase (c,stmts) = CCase (dataTag c) stmts
>         partition (t,stmts) ~(lits,constrs,dflts) =
>           case t of
>              LitCase c -> ((c,stmts) : lits,constrs,dflts)
>              ConstrCase c _ -> (lits,(c,stmts) : constrs,dflts)
>              DefaultCase -> (lits,constrs,stmts : dflts)
>         litPartition (Char c,stmts) ~(chars,ints,floats) =
>           ((c,stmts):chars,ints,floats)
>         litPartition (Int i,stmts) ~(chars,ints,floats) =
>           (chars,(i,stmts):ints,floats)
>         litPartition (Float f,stmts) ~(chars,ints,floats) =
>           (chars,ints,(f,stmts):floats)

> tagSwitch :: Name -> [CStmt] -> Maybe [CStmt] -> [CCase] -> CStmt
> tagSwitch v upd unboxed cases =
>   CLoop [unboxedSwitch unboxed (CSwitch (nodeTag v') allCases),CBreak]
>   where v' = show v
>         allCases = 
>           CCase "INDIR_TAG"
>             (CAssign (LVar v') (field v' "n.node") : upd ++ [CContinue]) :
>           cases ++ 
>           [CDefault [CBreak]]
>         unboxedSwitch (Just sts) switch
>           | null sts = CIf (isBoxed v') [switch] []
>           | otherwise = CIf (isUnboxed v') sts [switch]
>         unboxedSwitch Nothing switch = switch

> charSwitch :: Name -> [(Char,[CStmt])] -> CStmt
> charSwitch v cases =
>   CSwitch (CField (CExpr (show v)) "ch.ch")
>           ([CCase (show (ord c)) stmts | (c,stmts) <- cases] ++
>            [CDefault [CBreak]])

> intSwitch :: Name -> [(Int,[CStmt])] -> CStmt
> intSwitch v cases =
>   CSwitch (funCall "int_val" [show v])
>           ([CCase (show i) stmts | (i,stmts) <- cases] ++
>            [CDefault [CBreak]])

> floatSwitch :: Name -> [(Double,[CStmt])] -> [CStmt]
> floatSwitch v cases =
>   getFloat "d" (field (show v) "f") ++ foldr (match (CExpr "d")) [] cases
>   where match v (f,stmts) rest = [CIf (CRel v "==" (CFloat f)) stmts rest]

\end{verbatim}
The code for the \texttt{CPSApply} statement has to check the number
of missing arguments of the closure being applied. If there are too
few arguments, a new closure node is returned for the partial
application.  Otherwise, the closure is executed by pushing its
arguments onto the stack and jumping to the function's entry-point. If
the closure is applied to too many arguments, the code generated by
\texttt{applyExec} creates a return frame in the stack such that the
result of the application is applied to the excess arguments.
\begin{verbatim}

> apply :: [Name] -> Name -> [Name] -> [CStmt]
> apply vs0 v vs =
>   CLocalVar "unsigned int" "argc" (Just (funCall "closure_argc" [v'])) :
>   CLocalVar "int" "miss"
>     (Just (CSub (CField (CExpr v') "cl.info->arity") (CExpr "argc"))) :
>   CIf (CRel (CExpr "miss") ">" (CInt n)) (applyPartial vs0 n v) [] :
>   applyExec n v
>   where v' = show v
>         n = length vs

> applyPartial :: [Name] -> Int -> Name -> [CStmt]
> applyPartial vs0 n v =
>   CLocalVar "unsigned int" "sz" (Just (funCall "node_size" [v'])) :
>   CProcCall "CHECK_HEAP" [CAdd (CExpr "sz") (CInt n)] :
>   CAssign (LVar v') (asNode (CExpr "hp")) :
>   CIncrBy (LVar "hp") (CAdd (CExpr "sz") (CInt n)) :
>   wordCopy (CExpr v') (CExpr "sp[0]") "sz" :
>   CIncrBy (LField (LVar v') "cl.info") (CInt n) :
>   [CAssign (LElem (LField (LVar v') "cl.args")
>                   (CAdd (CExpr "argc") (CInt i)))
>            (CElem (CExpr "sp") (CInt (i+1))) | i <- [0 .. n-1]] ++
>   ret vs0 v Nothing
>   where v' = show v

> applyExec :: Int -> Name -> [CStmt]
> applyExec n v =
>   assertRel (CField (CField (CExpr v') "cl.info" `CAdd` CInt n)
>                     "node_info.tag") "==" (CExpr "CLOSURE_TAG") :
>   CIf (CRel (CExpr "miss") "==" (CInt n))
>       [CIncrBy (LVar "sp") (CInt 1),
>        CIf (CExpr "argc > 1") [CProcCall "CHECK_STACK" [CExpr "argc"]] []]
>       [CIf (CExpr "argc > 0") [CProcCall "CHECK_STACK" [CExpr "argc"]] [],
>        wordCopy (CExpr "sp") (CAdd (CExpr "sp") (CInt 1)) "miss",
>        CAssign (LElem (LVar "sp") (CExpr "miss"))
>                (asNode (CElem (CExpr applyTable)
>                               (CSub (CInt (n-1)) (CExpr "miss"))))] :
>   CDecrBy (LVar "sp") (CExpr "argc") :
>   wordCopy (CExpr "sp") (CField (CExpr v') "cl.args") "argc" :
>   gotoExpr (field v' "cl.info->entry") :
>   []
>   where v' = show v

\end{verbatim}
As a convenience to the user, we strip the decoration of auxiliary
function names introduced by the debugging transformation when the
name of a function is printed. In particular, the debugger adds the
prefix \texttt{\_debug\#} and a suffix \texttt{\#}$n$ to the name of
the transformed function. Note that the prefix is added to the
unqualified name.
\begin{verbatim}

> undecorate :: String -> String
> undecorate cs =
>   case break ('_' ==) cs of
>     (cs', "") -> dropSuffix cs'
>     (cs', ('_':cs''))
>       | "debug#" `isPrefixOf` cs'' -> cs' ++ undecorate (drop 6 cs'')
>       | otherwise -> cs' ++ '_' : undecorate cs''
>   where dropSuffix cs =
>           case break ('#' ==) cs of
>             (cs',"") -> cs'
>             (cs','#':cs'')
>               | all isDigit cs'' -> cs'
>               | otherwise -> cs' ++ '#' : dropSuffix cs''

\end{verbatim}
In order to avoid some trivial name conflicts with the standard C
library, we prefix the names of all Curry functions with two
underscores. The integer key of each CPS function is added to the
name, except for the function's main entry-point, whose key is
\texttt{0}.

The names of the info vector for a data constructor and the info table
for a function are constructed by appending the suffixes
\texttt{\_info} and \texttt{\_info\_table}, respectively, to the
name. The suffixes \texttt{\_const} and \texttt{\_function} are used
for constant constructors and functions, respectively.
\begin{verbatim}

> cName :: Name -> String
> cName x = "__" ++ show x

> cPrivName :: Name -> Int -> String
> cPrivName f n
>   | n == 0 = cName f
>   | otherwise = cName f ++ '_' : show n

> cpsName :: CPSFunction -> String
> cpsName (CPSFunction f n _ _ _ _) = cPrivName f n

> choicesArray :: ChoicesList -> String
> choicesArray (ChoicesList f n _) = cPrivName f n ++ "_choices"

> constArray, applyTable :: String
> constArray = "constants"
> applyTable = "apply_table"

> evalFunc, lazyFunc :: Name -> String
> evalFunc f = cName f ++ "_eval"
> lazyFunc f = cName f ++ "_lazy"

> dataInfo, infoTable :: Name -> String
> dataInfo c = cName c ++ "_info"
> lazyInfo f = cName f ++ "_suspend_info"
> infoTable f = cName f ++ "_info_table"

> functionInfo :: Name -> Int -> CExpr
> functionInfo f n
>   | isAp f = CAddr (CExpr (dataInfo f))
>   | otherwise = add (CExpr (infoTable f)) (CInt n)

> dataTag :: Name -> String
> dataTag c = cName c ++ "_tag"

> closVar :: Name -> String
> closVar v = show v ++ "_clos"

> isTuple :: Name -> Bool
> isTuple c = isTupleName (demangle c)
>   where isTupleName ('(':',':cs) = dropWhile (',' ==) cs == ")"
>         isTupleName _ = False

> tupleArity :: Name -> Int
> tupleArity c = arity (demangle c)
>   where arity ('(':',':cs)
>           | cs'' == ")" = length cs' + 2
>           where (cs',cs'') = partition (',' ==) cs
>         arity _ = error "internal error: tupleArity"

> isAp :: Name -> Bool
> isAp f = isApName (demangle f)
>   where isApName ('@':cs) = all isDigit cs
>         isApName _ = False

> apArity :: Name -> Int
> apArity f = arity (demangle f)
>   where arity ('@':cs)
>           | null cs = 1
>           | all isDigit cs = read cs
>         arity _ = error "internal error: applyArity"

> apName :: Int -> Name
> apName n = mangle ('@' : if n == 1 then "" else show n)

> constChar :: Char -> String
> constChar c = "char_table[" ++ show (ord c) ++ "]"

> constInt :: Int -> String
> constInt i = "int_" ++ mangle (show i)
>   where mangle ('-':cs) = 'M':cs
>         mangle cs = cs

> constFloat :: Double -> String
> constFloat f = "float_" ++ map mangle (show f)
>   where mangle '+' = 'P'
>         mangle '-' = 'M'
>         mangle '.' = '_'
>         mangle c = c

> constNode, constFunc :: Name -> String
> constNode c = cName c ++ "_node"
> constFunc f = cName f ++ "_function"

\end{verbatim}
Here are some convenience functions which simplify the construction of
the abstract syntax tree.
\begin{verbatim}

> asNode, asLabel, asString :: CExpr -> CExpr
> asNode = CCast "Node *"
> asLabel = CCast "Label"
> asString = CCast "const char *"

> goto :: String -> CStmt
> goto l = gotoExpr (CExpr l)

> gotoExpr :: CExpr -> CStmt
> gotoExpr l = CProcCall "GOTO" [l]

> tailCall :: String -> [String] -> CStmt
> tailCall f xs = gotoExpr (funCall f xs)

> funCall :: String -> [String] -> CExpr
> funCall f xs = CFunCall f (map CExpr xs)

> wordCopy :: CExpr -> CExpr -> String -> CStmt
> wordCopy e1 e2 sz =
>   CProcCall "memcpy" [e1,e2,CExpr sz `CMul` CExpr "word_size"]

> rtsAssert :: CExpr -> CStmt
> rtsAssert e = CProcCall "ASSERT" [e]

> rtsAssertList :: [CExpr] -> CStmt
> rtsAssertList es = rtsAssert (foldr1 (flip CRel "&&") es)

> assertRel :: CExpr -> String -> CExpr -> CStmt
> assertRel x op y = rtsAssert (CRel x op y)

> add :: CExpr -> CExpr -> CExpr
> add (CInt 0) y = y
> add x (CInt 0) = x
> add x y = x `CAdd` y

> getFloat :: String -> CExpr -> [CStmt]
> getFloat v e =
>   [CLocalVar "double" v Nothing,CProcCall "get_float_val" [CExpr v,e]]

> constRef :: String -> CExpr
> constRef = asNode . CAddr . CExpr

> isBoxed, isUnboxed :: String -> CExpr
> isBoxed v = funCall "is_boxed" [v]
> isUnboxed v = funCall "is_unboxed" [v]

> nodeTag :: String -> CExpr
> nodeTag v = field v "info->tag"

> field :: String -> String -> CExpr
> field v f = CField (CExpr v) f

\end{verbatim}
