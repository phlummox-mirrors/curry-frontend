
% $Id: CurrySyntax.lhs,v 1.43 2004/02/15 22:10:31 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
% Modified by Martin Engelke (men@informatik.uni-kiel.de)
%
\nwfilename{CurrySyntax.lhs}
\section{The Parse Tree}
This module provides the necessary data structures to maintain the
parsed representation of a Curry program.

\em{Note:} this modified version uses haskell type \texttt{Integer}
instead of \texttt{Int} for representing integer values. This allows
an unlimited range of integer constants in Curry programs.
\begin{verbatim}

> module CurrySyntax where
> import Ident
> import Position

\end{verbatim}
\paragraph{Modules}
\begin{verbatim}

> data Module = Module ModuleIdent (Maybe ExportSpec) [Decl] deriving (Eq,Show,Read)

> data ExportSpec = Exporting Position [Export] deriving (Eq,Show,Read)
> data Export =
>     Export         QualIdent                  -- f/T
>   | ExportTypeWith QualIdent [Ident]          -- T(C1,...,Cn)
>   | ExportTypeAll  QualIdent                  -- T(..)
>   | ExportModule   ModuleIdent
>   deriving (Eq,Show,Read)

\end{verbatim}
\paragraph{Module declarations}
\begin{verbatim}

> data ImportSpec =
>     Importing Position [Import]
>   | Hiding Position [Import]
>   deriving (Eq,Show,Read)
> data Import =
>     Import         Ident            -- f/T
>   | ImportTypeWith Ident [Ident]    -- T(C1,...,Cn)
>   | ImportTypeAll  Ident            -- T(..)
>   deriving (Eq,Show,Read)

> data Decl =
>     ImportDecl Position ModuleIdent Qualified (Maybe ModuleIdent)
>                (Maybe ImportSpec)
>   | InfixDecl Position Infix Integer [Ident]
>   | DataDecl Position Ident [Ident] [ConstrDecl]
>   | NewtypeDecl Position Ident [Ident] NewConstrDecl
>   | TypeDecl Position Ident [Ident] TypeExpr
>   | TypeSig Position [Ident] TypeExpr
>   | EvalAnnot Position [Ident] EvalAnnotation
>   | FunctionDecl Position Ident [Equation]
>   | ExternalDecl Position CallConv (Maybe String) Ident TypeExpr
>   | FlatExternalDecl Position [Ident]
>   | PatternDecl Position ConstrTerm Rhs
>   | ExtraVariables Position [Ident]
>   deriving (Eq,Show,Read)

> data ConstrDecl =
>     ConstrDecl Position [Ident] Ident [TypeExpr]
>   | ConOpDecl Position [Ident] TypeExpr Ident TypeExpr
>   deriving (Eq,Show,Read)
> data NewConstrDecl =
>   NewConstrDecl Position [Ident] Ident TypeExpr
>   deriving (Eq,Show,Read)

> type Qualified = Bool
> data Infix = InfixL | InfixR | Infix deriving (Eq,Show,Read)
> data EvalAnnotation = EvalRigid | EvalChoice deriving (Eq,Show,Read)
> data CallConv = CallConvPrimitive | CallConvCCall deriving (Eq,Show,Read)

\end{verbatim}
\paragraph{Module interfaces}
Interface declarations are restricted to type declarations and signatures. 
Note that an interface function declaration additionaly contains the 
function arity (= number of parameters) in order to generate
correct FlatCurry function applications.
\begin{verbatim}

> data Interface = Interface ModuleIdent [IDecl] deriving (Eq,Show,Read)

> data IDecl =
>     IImportDecl Position ModuleIdent
>   | IInfixDecl Position Infix Integer QualIdent
>   | HidingDataDecl Position Ident [Ident] 
>   | IDataDecl Position QualIdent [Ident] [Maybe ConstrDecl]
>   | INewtypeDecl Position QualIdent [Ident] NewConstrDecl
>   | ITypeDecl Position QualIdent [Ident] TypeExpr
>   | IFunctionDecl Position QualIdent Int TypeExpr
>   deriving (Eq,Show,Read)

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> data TypeExpr =
>     ConstructorType QualIdent [TypeExpr]
>   | VariableType Ident
>   | TupleType [TypeExpr]
>   | ListType TypeExpr
>   | ArrowType TypeExpr TypeExpr
>   | RecordType [([Ident],TypeExpr)] (Maybe TypeExpr) 
>     -- {l1 :: t1,...,ln :: tn | r}
>   deriving (Eq,Show,Read)

\end{verbatim}
\paragraph{Functions}
\begin{verbatim}

> data Equation = Equation Position Lhs Rhs deriving (Eq,Show,Read)
> data Lhs =
>     FunLhs Ident [ConstrTerm]
>   | OpLhs ConstrTerm Ident ConstrTerm
>   | ApLhs Lhs [ConstrTerm]
>   deriving (Eq,Show,Read)
> data Rhs =
>     SimpleRhs Position Expression [Decl]
>   | GuardedRhs [CondExpr] [Decl]
>   deriving (Eq,Show,Read)
> data CondExpr = CondExpr Position Expression Expression deriving (Eq,Show,Read)

> flatLhs :: Lhs -> (Ident,[ConstrTerm])
> flatLhs lhs = flat lhs []
>   where flat (FunLhs f ts) ts' = (f,ts ++ ts')
>         flat (OpLhs t1 op t2) ts = (op,t1:t2:ts)
>         flat (ApLhs lhs ts) ts' = flat lhs (ts ++ ts')

\end{verbatim}
\paragraph{Literals} The \texttt{Ident} argument of an \texttt{Int}
literal is used for supporting ad-hoc polymorphism on integer
numbers. An integer literal can be used either as an integer number or
as a floating-point number depending on its context. The compiler uses
the identifier of the \texttt{Int} literal for maintaining its type.
\begin{verbatim}

> data Literal =
>     Char Char                         -- should be Int to handle Unicode
>   | Int Ident Integer
>   | Float Double
>   | String String                     -- should be [Int] to handle Unicode
>   deriving (Eq,Show,Read)

\end{verbatim}
\paragraph{Patterns}
\begin{verbatim}

> data ConstrTerm =
>     LiteralPattern Literal
>   | NegativePattern Ident Literal
>   | VariablePattern Ident
>   | ConstructorPattern QualIdent [ConstrTerm]
>   | InfixPattern ConstrTerm QualIdent ConstrTerm
>   | ParenPattern ConstrTerm
>   | TuplePattern [ConstrTerm]
>   | ListPattern [ConstrTerm]
>   | AsPattern Ident ConstrTerm
>   | LazyPattern ConstrTerm
>   | FunctionPattern QualIdent [ConstrTerm]
>   | InfixFuncPattern ConstrTerm QualIdent ConstrTerm
>   | RecordPattern [Field ConstrTerm] (Maybe ConstrTerm)  
>         -- {l1 = p1, ..., ln = pn}  oder {l1 = p1, ..., ln = pn | p}
>   deriving (Eq,Show,Read)

\end{verbatim}
\paragraph{Expressions}
\begin{verbatim}

> data Expression =
>     Literal Literal
>   | Variable QualIdent
>   | Constructor QualIdent
>   | Paren Expression
>   | Typed Expression TypeExpr
>   | Tuple [Expression]
>   | List [Expression]
>   | ListCompr Expression [Statement]
>   | EnumFrom Expression
>   | EnumFromThen Expression Expression
>   | EnumFromTo Expression Expression
>   | EnumFromThenTo Expression Expression Expression
>   | UnaryMinus Ident Expression
>   | Apply Expression Expression
>   | InfixApply Expression InfixOp Expression
>   | LeftSection Expression InfixOp
>   | RightSection InfixOp Expression
>   | Lambda [ConstrTerm] Expression
>   | Let [Decl] Expression
>   | Do [Statement] Expression
>   | IfThenElse Expression Expression Expression
>   | Case Expression [Alt]
>   | RecordConstr [Field Expression]            -- {l1 = e1,...,ln = en}
>   | RecordSelection Expression Ident           -- e -> l
>   | RecordUpdate [Field Expression] Expression -- {l1 := e1,...,ln := en | e}
>   deriving (Eq,Show,Read)

> data InfixOp = InfixOp QualIdent | InfixConstr QualIdent deriving (Eq,Show,Read)

> data Statement =
>     StmtExpr Expression
>   | StmtDecl [Decl]
>   | StmtBind ConstrTerm Expression
>   deriving (Eq,Show,Read)

> data Alt = Alt Position ConstrTerm Rhs deriving (Eq,Show,Read)

> data Field a = Field Position Ident a deriving (Eq, Show,Read)

> fieldLabel :: Field a -> Ident
> fieldLabel (Field _ l _) = l

> fieldTerm :: Field a -> a
> fieldTerm (Field _ _ t) = t

> field2Tuple :: Field a -> (Ident,a)
> field2Tuple (Field _ l t) = (l,t)

> opName :: InfixOp -> QualIdent
> opName (InfixOp op) = op
> opName (InfixConstr c) = c

\end{verbatim}
\paragraph{Goals}
A goal is equivalent to an unconditional right hand side of an equation.
\begin{verbatim}

> data Goal = Goal Position Expression [Decl] deriving (Eq,Show,Read)

\end{verbatim}
