% -*- LaTeX -*-
% $Id: CPS.lhs,v 2.3 2004/05/02 09:24:34 wlux Exp $
%
% Copyright (c) 2003-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CPS.lhs}
\section{Continuation Passing Style}\label{sec:cps}
\begin{verbatim}

> module CPS(CPSFunction(..),CaseBlock(..),CPSStmt(..),ChoicesList(..),
>            cpsFunction, cpsApply, cpsVars, fromCaseBlock, caseBlockTag,
>            fresh) where
> import Cam
> import List
> import Set
> import SCC

\end{verbatim}
In order to implement concurrent threads and the encapsulated search
in a portable way, the compiler first transforms every abstract
machine code function into continuation passing style (CPS). Thus, all
return addresses and in particular the addresses where a computation
is resumed after a thread switch or in an encapsulated search
correspond to the address of a function in the C code. During the
translation, the compiler also adds code to instantiate unbound
variables in a flexible switch statement and to implement stability
when it is enabled.

Special code is generated for the private functions that implement
partial applications of tuple constructors and for the functions
\texttt{@}$_n$.

A CPS function is identified by the name of the function from which it
was translated and an integer number that enumerates all CPS functions
into which an abstract machine code function was translated.  A CPS
function has no free variables, i.e., its argument list must name all
variables that are used in the body. The body of a CPS function
consists of a sequence of -- possibly mutually recursive -- variable
assignments and a statement. The assignments are split into minimal
recursive groups, as this eases the detection of constants in recursive
pattern declarations, e.g., \verb|let { xs=0:ys; ys=1:xs } in |\dots{}
The \texttt{(Maybe String)} argument of a \texttt{CPSFunction} is used
to define functions which are compiled only if a particular
C-preprocessor constant is defined.
\begin{verbatim}

> data CPSFunction =
>   CPSFunction Name Int (Maybe String) [Name] [[Bind]] CPSStmt
>   deriving Show
> data CPSStmt =
>     CPSJump CPSFunction
>   | CPSReturn Name (Maybe CPSFunction)
>   | CPSEnter Name (Maybe CPSFunction)
>   | CPSExec Name [Name] (Maybe CPSFunction)
>   | CPSLock Name CPSStmt
>   | CPSUpdate Name Name CPSStmt
>   | CPSApply Name [Name]
>   | CPSBind Name Name CPSFunction
>   | CPSDelay Name CPSFunction
>   | CPSYield (Maybe Name) CPSStmt CPSFunction
>   | CPSSwitch Bool Name (Maybe CPSStmt) [CaseBlock]
>   | CPSLocalSwitch Name CPSStmt CaseBlock
>   | CPSChoices ChoicesList
>   deriving Show
> data CaseBlock = CaseBlock Int Tag [Name] [[Bind]] CPSStmt deriving Show
> data ChoicesList = ChoicesList Name Int [CPSFunction] deriving Show

> instance Eq CPSFunction where
>   CPSFunction f1 n1 _ _ _ _ == CPSFunction f2 n2 _ _ _ _ =
>     f1 == f2 && n1 == n2
> instance Ord CPSFunction where
>   CPSFunction f1 n1 _ _ _ _ `compare` CPSFunction f2 n2 _ _ _ _ =
>     case f1 `compare` f2 of
>       EQ -> n1 `compare` n2
>       ne -> ne

> cpsFunction :: Name -> [Name] -> Stmt -> [CPSFunction]
> cpsFunction f vs st = linearize (snd (cps f Nothing vs 0 st))

> cpsApply :: Name -> [Name] -> [CPSFunction]
> cpsApply f vs@(v:vs') = [k0,k1]
>   where k0 = CPSFunction f 0 Nothing vs [] (CPSEnter v (Just k1))
>         k1 = CPSFunction f 1 Nothing vs []
>                (CPSSwitch False v (Just (CPSDelay v k1))
>                   [CaseBlock 1 DefaultCase vs [] (CPSApply v vs')])

> cpsVars :: CPSFunction -> [Name]
> cpsVars (CPSFunction _ _ _ vs _ _) = vs

> caseBlockTag :: CaseBlock -> Tag
> caseBlockTag (CaseBlock _ t _ _ _) = t

> fromCaseBlock :: Name -> CaseBlock -> CPSFunction
> fromCaseBlock f (CaseBlock n _ vs dss st) = CPSFunction f n Nothing vs dss st

\end{verbatim}
The transformation into CPS is implemented by a top-down algorithm.
The abstract machine code statements \texttt{return}, \texttt{enter},
and \texttt{exec} are transformed directly into their CPS equivalents.
In the case of a \texttt{seq} statement, a new continuation is created
for the second statement using the bound variable as the first input
argument. The declarations of a \texttt{let} statement are split into
minimal binding groups and collected in the resulting CPS function.

The transformation of a \texttt{switch} statement is more
complicated because the compiler has to introduce auxiliary code for
matching an unbound variable. Furthermore, a \texttt{CPSSwitch} cannot
be inlined into the cases of another switch and it must not be
preceded by variable assignments because these assignments were
repeated and new nodes created after instantiating an unbound variable.
In both cases, the compiler introduces a new function for the switch
and uses a \texttt{CPSJump} to that function. This is implemented in
\texttt{cpsJumpSwitch}. Depending on the context either this function
or \texttt{cpsSwitch} is passed as an argument to \texttt{cpsStmt} and
used for translating the \texttt{switch} statement.

The translation of a \texttt{choices} statement has to ensure that all
alternatives use the same input variables so that the runtime system
does not need to construct closures for each of them.

Note that the transformation ensures that the unique identifier of
every CPS function is greater than that of its predecessor. This is
used below in order to transform the CPS graph into a linear sequence
of CPS functions.
\begin{verbatim}

> cps :: Name -> Maybe CPSFunction -> [Name] -> Int -> Stmt
>     -> (Int,CPSFunction)
> cps f k ws n st =
>   cpsStmt cpsSwitch f k (CPSFunction f n Nothing vs) (n + 1) st
>   where vs = nub $ ws ++ freeVars st (contVars k)                        -- $

> cpsCase :: Name -> Maybe CPSFunction -> [Name] -> Int -> Case
>         -> (Int,CaseBlock)
> cpsCase f k ws n (Case t st) =
>   cpsStmt cpsJumpSwitch f k (CaseBlock n t ws) (n + 1) st

> cpsStmt :: (Name -> Maybe CPSFunction -> (CPSStmt -> a) -> Int -> RF -> Name 
>             -> [Case] -> (Int,a))
>         -> Name -> Maybe CPSFunction -> ([[Bind]] -> CPSStmt -> a)
>         -> Int -> Stmt -> (Int,a)
> cpsStmt _ _ k g n (Return v) = (n,g [] (CPSReturn v k))
> cpsStmt _ _ k g n (Enter v) = (n,g [] (CPSEnter v k))
> cpsStmt _ _ k g n (Exec f vs) = (n,g [] (CPSExec f vs k))
> cpsStmt _ f k g n (Lock v st) =
>   cpsStmt cpsJumpSwitch f k (\ds st -> g ds (CPSLock v st)) n st
> cpsStmt _ f k g n (Update v1 v2 st) =
>   cpsStmt cpsJumpSwitch f k (\ds st -> g ds (CPSUpdate v1 v2 st)) n st
> cpsStmt cpsSwitch f k g n (Seq v st1 st2) = (n'',k')
>   where (n',k') = cpsStmt cpsSwitch f (Just k'') g n st1
>         (n'',k'') = cps f k [v] n' st2
> cpsStmt _ f k g n (Let ds st) =
>   cpsStmt cpsJumpSwitch f k (g . (scc bound free ds ++)) n st
>   where bound (Bind v _) = [v]
>         free (Bind _ n) = exprVars n
> cpsStmt cpsSwitch f k g n (Switch rf v cases) =
>   cpsSwitch f k (g []) n rf v cases
> cpsStmt _ f k g n (Choices alts) = (n'',k')
>   where (n',k') = cpsChoose f g vs n Nothing id ks
>         (n'',ks) = mapAccumL (cps f k vs) n' alts
>         vs = nub $ freeVars (Choices alts) (contVars k)                  -- $

> cpsJumpSwitch :: Name -> Maybe CPSFunction -> (CPSStmt -> a) -> Int
>               -> RF -> Name -> [Case] -> (Int,a)
> cpsJumpSwitch f k g n rf v cases = (n',g (CPSJump k'))
>   where (n',k') =
>           cpsSwitch f k (CPSFunction f n Nothing vs []) (n + 1) rf v cases
>         vs = nub $ v : freeVars (Switch rf v cases) (contVars k)         -- $

> cpsSwitch :: Name -> Maybe CPSFunction -> (CPSStmt -> CPSFunction) -> Int
>           -> RF -> Name -> [Case] -> (Int,CPSFunction)
> cpsSwitch f k g n rf v cases = (n'',k')
>   where k' = g (CPSSwitch ub v vcase cases')
>         (n',vcase) = cpsVarCase ub f k' ws n rf v ts
>         (n'',cases') = mapAccumL (cpsCase f k ws) n' cases
>         ws = cpsVars k'
>         ts = [t | Case t _ <- cases, t /= DefaultCase]
>         ub = unboxedSwitch ts

> cpsVarCase :: Bool -> Name -> CPSFunction -> [Name] -> Int -> RF -> Name
>            -> [Tag] -> (Int,Maybe CPSStmt)
> cpsVarCase _ _ k _ n Rigid v _ = (n,Just (CPSDelay v k))
> cpsVarCase ub f k ws n Flex v ts
>   | null ts = (n,Nothing)
>   | otherwise = (n',Just (CPSLocalSwitch v (CPSDelay v k) k'))
>   where (n',k') = cpsFlexCase ub f k ws n v ts

> cpsFlexCase :: Bool -> Name -> CPSFunction -> [Name] -> Int -> Name
>             -> [Tag] -> (Int,CaseBlock)
> cpsFlexCase _ _ k ws n v [t] =
>   cpsFresh k (\n -> CaseBlock n DefaultCase ws) v n t
> cpsFlexCase ub f k ws n v ts = (n'',k')
>   where (n',k') = cpsChoose f (CaseBlock n DefaultCase ws) ws (n + 1)
>                             (Just v) checkVar ks
>         (n'',ks) =
>           mapAccumL (cpsFresh k (\n -> CPSFunction f n Nothing ws) v) n' ts
>         checkVar st = CPSSwitch ub v (Just st)
>                                 [CaseBlock n DefaultCase ws [] (CPSJump k)]

> cpsFresh :: CPSFunction -> (Int -> [[Bind]] -> CPSStmt -> a) -> Name -> Int
>          -> Tag -> (Int,a)
> cpsFresh k g v n t = (n + 1,g n (fresh v' t) (CPSBind v v' k))
>   where v' = Name "_new"

> cpsChoose :: Name -> ([[Bind]] -> CPSStmt -> a) -> [Name] -> Int
>           -> Maybe Name -> (CPSStmt -> CPSStmt) -> [CPSFunction] -> (Int,a)
> cpsChoose f g ws n v h ks = (n + 1,g [] (CPSYield v st k))
>   where k = CPSFunction f n (Just "YIELD_NONDET") ws [] (h st)
>         st = CPSChoices (ChoicesList f (n - 1) ks)

> unboxedSwitch :: [Tag] -> Bool
> unboxedSwitch [] = True
> unboxedSwitch (LitCase (Int _) : _) = True
> unboxedSwitch (LitCase _ : _) = False
> unboxedSwitch (ConstrCase _ _ : _) = False
> unboxedSwitch (DefaultCase : cases) = unboxedSwitch cases

> contVars :: Maybe CPSFunction -> [Name]
> contVars = maybe [] (tail . cpsVars)

> tagVars :: Tag -> [Name]
> tagVars (LitCase _) = []
> tagVars (ConstrCase _ vs) = vs
> tagVars DefaultCase = []

> exprVars :: Expr -> [Name]
> exprVars (Lit _) = []
> exprVars (Constr _ vs) = vs
> exprVars (Closure _ vs) = vs
> exprVars (Lazy _ vs) = vs
> exprVars Free = []
> exprVars (Ref v) = [v]

> freeVars :: Stmt -> [Name] -> [Name]
> freeVars (Return v) vs = v : vs
> freeVars (Enter v) vs = v : vs
> freeVars (Exec _ vs) vs' = vs ++ vs'
> freeVars (Lock v st) vs = v : freeVars st vs
> freeVars (Update v1 v2 st) vs = v1 : v2 : freeVars st vs
> freeVars (Seq v st1 st2) vs =
>   freeVars st1 $ filter (v /=) $ freeVars st2 vs
> freeVars (Let ds st) vs = filter (`notElemSet` bvs) (fvs ++ freeVars st vs)
>   where bvs = fromListSet [v | Bind v _ <- ds]
>         fvs = concat [exprVars n | Bind _ n <- ds]
> freeVars (Switch _ v cases) vs = v : concatMap (flip freeVarsCase vs) cases
>   where freeVarsCase (Case t st) vs =
>           filter (`notElemSet` fromListSet (tagVars t)) (freeVars st vs)
> freeVars (Choices alts) vs = concatMap (flip freeVars vs) alts

> fresh :: Name -> Tag -> [[Bind]]
> fresh v (LitCase c) = [[Bind v (Lit c)]]
> fresh v (ConstrCase c vs) = map freshVar vs ++ [[Bind v (Constr c vs)]]
>   where freshVar v = [Bind v Free]

\end{verbatim}
After computing the CPS graph, the CPS functions are linearized in
ascending order. The code uses the unique identifier in order to avoid
duplication of shared continuations.
\begin{verbatim}

> linearize :: CPSFunction -> [CPSFunction]
> linearize = linearizeCont minBound

> linearizeCont :: Int -> CPSFunction -> [CPSFunction]
> linearizeCont n0 (CPSFunction f n c vs dss st)
>   | n > n0 = CPSFunction f n c vs dss st : linearizeStmt n st
>   | otherwise = []

> linearizeStmt :: Int -> CPSStmt -> [CPSFunction]
> linearizeStmt n (CPSJump k) = linearizeCont n k
> linearizeStmt n (CPSReturn _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSEnter _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSExec _ _ k) = maybe [] (linearizeCont n) k
> linearizeStmt n (CPSLock _ st) = linearizeStmt n st
> linearizeStmt n (CPSUpdate _ _ st) = linearizeStmt n st
> linearizeStmt _ (CPSApply _ _) = []
> linearizeStmt n (CPSBind _ _ k) = linearizeCont n k
> linearizeStmt n (CPSDelay _ k) = linearizeCont n k
> linearizeStmt n (CPSYield _ st k) =
>   linMerge [linearizeCont n k,linearizeStmt n st]
> linearizeStmt n (CPSSwitch _ _ vcase cases) =
>   linMerge (maybe [] (linearizeStmt n) vcase :
>             [linearizeStmt n' st | CaseBlock n' _ _ _ st <- cases])
> linearizeStmt n (CPSLocalSwitch _ st (CaseBlock n' _ _ _ st')) =
>   linMerge [linearizeStmt n st,linearizeStmt n' st']
> linearizeStmt n (CPSChoices (ChoicesList _ _ ks)) =
>   linMerge (map (linearizeCont n) ks)

> linMerge :: [[CPSFunction]] -> [CPSFunction]
> linMerge kss = merge (sort kss)
>   where merge [] = []
>         merge [ks] = ks
>         merge ([] : kss) = merge kss
>         merge ((k:ks) : kss) = k : merge (ks : filter ((k /=) . head) kss)

\end{verbatim}
