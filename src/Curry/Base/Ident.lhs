> {-# LANGUAGE DeriveDataTypeable #-}

% $Id: Ident.lhs,v 1.21 2004/10/29 13:08:09 wlux Exp $
%
% Copyright (c) 1999-2004, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Ident.lhs}
\section{Identifiers}
This module provides the implementation of identifiers and some
utility functions for identifiers, which are used at various places in
the compiler.

Identifiers comprise the name of the denoted entity and an \emph{id},
which can be used for renaming identifiers, e.g., in order to resolve
name conflicts between identifiers from different scopes. An
identifier with an \emph{id} $0$ is considered as not being renamed
and, hence, its \emph{id} will not be shown.

\ToDo{Probably we should use \texttt{Integer} for the \emph{id}s.}

Qualified identifiers may optionally be prefixed by a module
name. \textbf{The order of the cases \texttt{UnqualIdent} and
\texttt{QualIdent} is important. Some parts of the compiler rely on
the fact that all qualified identifiers are greater than any
unqualified identifier.}
\begin{verbatim}

> module Curry.Base.Ident(Ident(..),QualIdent(..),ModuleIdent,SrcRefOf(..),
>                         mkIdent, name, qualName, uniqueId,
>                         renameIdent, unRenameIdent,
>                         mkMIdent, moduleName, moduleQualifiers,
>                         isInfixOp, isQInfixOp,
>                         qualify, qualifyWith, qualQualify,
>                         isQualified, unqualify, qualUnqualify,
>                         localIdent, splitQualIdent,
>                         emptyMIdent, mainMIdent,preludeMIdent,
>                         anonId,unitId,boolId,charId,intId,floatId,listId,ioId,
>                         successId,trueId,falseId,nilId,consId,mainId,
>                         tupleId,isTupleId,tupleArity,
>                         minusId,fminusId,updIdentName,
>                         qUnitId,qBoolId,qCharId,qIntId,qFloatId,qListId,qIOId,
>                         qSuccessId,qTrueId,qFalseId,qNilId,qConsId,
>                         qTupleId,isQTupleId,qTupleArity,
>                         fpSelectorId,isFpSelectorId,isQualFpSelectorId,
>                         recSelectorId,qualRecSelectorId,
>                         recUpdateId, qualRecUpdateId, recordExtId, labelExtId,
>                         isRecordExtId, isLabelExtId, fromRecordExtId, fromLabelExtId,
>                         renameLabel,
>                         recordExt, labelExt, mkLabelIdent,hasPositionIdent,

                         showsIdent,showsQualIdent,showsModuleIdent,

>                         addPositionIdent, removePositionIdent, positionOfIdent,
>                         addPositionModuleIdent, removePositionModuleIdent,addRef,addRefId,
>                         positionOfModuleIdent,positionOfQualIdent,updQualIdent ) where

> import Data.Char
> import Data.List
> import Data.Maybe
> import Data.Generics

> import Curry.Base.Position


> data Ident = Ident String Int 
>            | IdentPosition Position String Int
>            deriving (Read,Data,Typeable)
>
> data QualIdent = UnqualIdent Ident
>                | QualIdent ModuleIdent Ident
>                  deriving (Eq,Ord,Read,Data,Typeable)
> data ModuleIdent = ModuleIdent [String] 
>                   |ModuleIdentPosition Position [String] deriving (Data,Typeable)

> instance Eq Ident where
>    ident1 == ident2 = name ident1 == name     ident2 && 
>                   uniqueId ident1 == uniqueId ident2

> instance Ord ModuleIdent where
>    mident1 `compare` mident2 =
>        moduleQualifiers mident1 `compare` moduleQualifiers mident2

> instance Eq ModuleIdent where
>    mident1 == mident2 = moduleQualifiers mident1 == moduleQualifiers mident2 

> instance Read ModuleIdent where
>   readsPrec p s = [ (mkMIdent [m],s') | (m,s') <- readsPrec p s ]

> instance Ord Ident where
>    ident1 `compare` ident2 =
>        (name ident1,uniqueId ident1) `compare` (name ident2,uniqueId ident2)

> instance Show Ident where
>   showsPrec _ (Ident x n)
>     | n == 0 = showString x
>     | otherwise = showString x . showChar '.' . shows n
>   showsPrec _ (IdentPosition _ x n)
>     | n == 0 = showString x
>     | otherwise = showString x . showChar '.' . shows n

> instance Show QualIdent where
>   showsPrec _ (UnqualIdent x) = shows x
>   showsPrec _ (QualIdent m x) = shows m . showChar '.' . shows x

> instance Show ModuleIdent where
>   showsPrec _ m = showString (moduleName m)


> hasPositionIdent :: Ident -> Bool
> hasPositionIdent (Ident _ _ ) = False
> hasPositionIdent (IdentPosition _ _ _) = True

> addPositionIdent :: Position -> Ident -> Ident
> addPositionIdent pos (Ident x n) = IdentPosition pos x n
> addPositionIdent AST{ast=sr} (IdentPosition pos x n) = 
>   IdentPosition pos{ast=sr} x n
> addPositionIdent pos (IdentPosition _ x n) = 
>   IdentPosition pos x n

> removePositionIdent :: Ident -> Ident
> removePositionIdent (Ident x n) = (Ident x n)
> removePositionIdent (IdentPosition _ x n) = (Ident x n)

> positionOfIdent :: Ident -> Position
> positionOfIdent (Ident _ _) = noPos
> positionOfIdent (IdentPosition pos _ _) = pos

> addPositionModuleIdent :: Position -> ModuleIdent -> ModuleIdent
> addPositionModuleIdent pos (ModuleIdent x) = ModuleIdentPosition pos x 
> addPositionModuleIdent pos (ModuleIdentPosition _ x) = ModuleIdentPosition pos x 

> removePositionModuleIdent :: ModuleIdent -> ModuleIdent
> removePositionModuleIdent (ModuleIdent x) = (ModuleIdent x)
> removePositionModuleIdent (ModuleIdentPosition _ x) = (ModuleIdent x)

> positionOfModuleIdent :: ModuleIdent -> Position
> positionOfModuleIdent (ModuleIdent _) = noPos
> positionOfModuleIdent (ModuleIdentPosition pos _) = pos

> positionOfQualIdent :: QualIdent -> Position
> positionOfQualIdent = positionOfIdent . snd . splitQualIdent

> mkIdent :: String -> Ident
> mkIdent x = Ident x 0

> name :: Ident -> String
> name (Ident x _) = x
> name (IdentPosition _ x _) = x

> qualName :: QualIdent -> String
> qualName (UnqualIdent x) = name x
> qualName (QualIdent m x) = moduleName m ++ "." ++ name x

> uniqueId :: Ident -> Int
> uniqueId (Ident _ n) = n
> uniqueId (IdentPosition _ _ n) = n

> renameIdent :: Ident -> Int -> Ident
> renameIdent (Ident x _) n = Ident x n
> renameIdent (IdentPosition p x _) n = IdentPosition p x n

> unRenameIdent :: Ident -> Ident
> unRenameIdent (Ident x _) = Ident x 0
> unRenameIdent (IdentPosition p x _) = IdentPosition p x 0

> mkMIdent :: [String] -> ModuleIdent
> mkMIdent = ModuleIdent

> moduleName :: ModuleIdent -> String
> moduleName (ModuleIdent xs) = concat (intersperse "." xs)
> moduleName (ModuleIdentPosition _ xs) = concat (intersperse "." xs)

> moduleQualifiers :: ModuleIdent -> [String]
> moduleQualifiers (ModuleIdent xs) = xs
> moduleQualifiers (ModuleIdentPosition _ xs) = xs

> isInfixOp :: Ident -> Bool
> isInfixOp (Ident ('<':c:cs) _)=
>   last (c:cs) /= '>' || not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident (c:_) _) = not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident _ _) = False -- error "Zero-length identifier"
> isInfixOp x@(IdentPosition _ _ _) = isInfixOp $ removePositionIdent x

> isQInfixOp :: QualIdent -> Bool
> isQInfixOp (UnqualIdent x) = isInfixOp x
> isQInfixOp (QualIdent _ x) = isInfixOp x

\end{verbatim}
The functions \texttt{qualify} and \texttt{qualifyWith} convert an
unqualified identifier into a qualified identifier (without and with a
given module prefix, respectively).
\begin{verbatim}

> qualify :: Ident -> QualIdent
> qualify = UnqualIdent

> qualifyWith :: ModuleIdent -> Ident -> QualIdent
> qualifyWith = QualIdent

> qualQualify :: ModuleIdent -> QualIdent -> QualIdent
> qualQualify m (UnqualIdent x) = QualIdent m x
> qualQualify _ x = x

> isQualified :: QualIdent -> Bool
> isQualified (UnqualIdent _) = False
> isQualified (QualIdent _ _) = True

> unqualify :: QualIdent -> Ident
> unqualify (UnqualIdent x) = x
> unqualify (QualIdent _ x) = x

> qualUnqualify :: ModuleIdent -> QualIdent -> QualIdent
> qualUnqualify m (UnqualIdent x) = UnqualIdent x
> qualUnqualify m (QualIdent m' x)
>   | m == m' = UnqualIdent x
>   | otherwise = QualIdent m' x

> localIdent :: ModuleIdent -> QualIdent -> Maybe Ident
> localIdent _ (UnqualIdent x) = Just x
> localIdent m (QualIdent m' x)
>   | m == m' = Just x
>   | otherwise = Nothing

> splitQualIdent :: QualIdent -> (Maybe ModuleIdent,Ident)
> splitQualIdent (UnqualIdent x) = (Nothing,x)
> splitQualIdent (QualIdent m x) = (Just m,x)

> updQualIdent :: (ModuleIdent -> ModuleIdent) -> (Ident -> Ident) -> QualIdent -> QualIdent
> updQualIdent _ g (UnqualIdent x) = UnqualIdent (g x)
> updQualIdent f g (QualIdent m x) = QualIdent (f m) (g x)

> addRef :: SrcRef -> QualIdent -> QualIdent
> addRef r = updQualIdent id (addRefId r)

> addRefId :: SrcRef -> Ident -> Ident
> addRefId r = addPositionIdent (AST r)

\end{verbatim}
A few identifiers a predefined here.
\begin{verbatim}

> emptyMIdent, mainMIdent, preludeMIdent :: ModuleIdent
> emptyMIdent   = ModuleIdent []
> mainMIdent    = ModuleIdent ["main"]
> preludeMIdent = ModuleIdent ["Prelude"]

> anonId :: Ident
> anonId = Ident "_" 0

> unitId, boolId, charId, intId, floatId, listId, ioId, successId :: Ident
> unitId    = Ident "()" 0
> boolId    = Ident "Bool" 0
> charId    = Ident "Char" 0
> intId     = Ident "Int" 0
> floatId   = Ident "Float" 0
> listId    = Ident "[]" 0
> ioId      = Ident "IO" 0
> successId = Ident "Success" 0

> trueId, falseId, nilId, consId :: Ident
> trueId  = Ident "True" 0
> falseId = Ident "False" 0
> nilId   = Ident "[]" 0
> consId  = Ident ":" 0

> tupleId :: Int -> Ident
> tupleId n
>   | n >= 2 = Ident ("(" ++ replicate (n - 1) ',' ++ ")") 0
>   | otherwise = error "internal error: tupleId"

> isTupleId :: Ident -> Bool
> isTupleId x = n > 1 && x == tupleId n
>   where n = length (name x) - 1

> tupleArity :: Ident -> Int
> tupleArity x
>   | n > 1 && x == tupleId n = n
>   | otherwise = error "internal error: tupleArity"
>   where n = length (name x) - 1

> mainId, minusId, fminusId :: Ident
> mainId = Ident "main" 0
> minusId = Ident "-" 0
> fminusId = Ident "-." 0

> qUnitId, qNilId, qConsId, qListId :: QualIdent
> qUnitId = UnqualIdent unitId
> qListId = UnqualIdent listId
> qNilId  = UnqualIdent nilId
> qConsId = UnqualIdent consId

> qBoolId, qCharId, qIntId, qFloatId, qSuccessId, qIOId :: QualIdent
> qBoolId = QualIdent preludeMIdent boolId
> qCharId = QualIdent preludeMIdent charId
> qIntId = QualIdent preludeMIdent intId
> qFloatId = QualIdent preludeMIdent floatId
> qSuccessId = QualIdent preludeMIdent successId
> qIOId = QualIdent preludeMIdent ioId

> qTrueId, qFalseId :: QualIdent
> qTrueId = QualIdent preludeMIdent trueId
> qFalseId = QualIdent preludeMIdent falseId

> qTupleId :: Int -> QualIdent
> qTupleId = UnqualIdent . tupleId

> isQTupleId :: QualIdent -> Bool
> isQTupleId = isTupleId . unqualify

> qTupleArity :: QualIdent -> Int
> qTupleArity = tupleArity . unqualify

\end{verbatim}
Micellaneous function for generating and testing extended identifiers.
\begin{verbatim}

> fpSelectorId :: Int -> Ident
> fpSelectorId n = Ident (fpSelExt ++ show n) 0

> isFpSelectorId :: Ident -> Bool
> isFpSelectorId f = any (fpSelExt `isPrefixOf`) (tails (name f))

> isQualFpSelectorId :: QualIdent -> Bool
> isQualFpSelectorId = isFpSelectorId . unqualify

> recSelectorId :: QualIdent -> Ident -> Ident
> recSelectorId r l =
>   mkIdent (recSelExt ++ name (unqualify r) ++ "." ++ name l)

> qualRecSelectorId :: ModuleIdent -> QualIdent -> Ident -> QualIdent
> qualRecSelectorId m r l = qualifyWith m' (recSelectorId r l)
>   where m' = (fromMaybe m (fst (splitQualIdent r)))

> recUpdateId :: QualIdent -> Ident -> Ident
> recUpdateId r l = 
>   mkIdent (recUpdExt ++ name (unqualify r) ++ "." ++ name l)

> qualRecUpdateId :: ModuleIdent -> QualIdent -> Ident -> QualIdent
> qualRecUpdateId m r l = qualifyWith m' (recUpdateId r l)
>   where m' = (fromMaybe m (fst (splitQualIdent r)))

> recordExtId :: Ident -> Ident
> recordExtId r = mkIdent (recordExt ++ name r)

> labelExtId :: Ident -> Ident
> labelExtId l = mkIdent (labelExt ++ name l)

> fromRecordExtId :: Ident -> Ident
> fromRecordExtId r 
>   | p == recordExt = mkIdent r'
>   | otherwise = r
>  where (p,r') = splitAt (length recordExt) (name r)

> fromLabelExtId :: Ident -> Ident
> fromLabelExtId l 
>   | p == labelExt = mkIdent l'
>   | otherwise = l
>  where (p,l') = splitAt (length labelExt) (name l)

> isRecordExtId :: Ident -> Bool
> isRecordExtId r = recordExt `isPrefixOf` name r

> isLabelExtId :: Ident -> Bool
> isLabelExtId l = labelExt `isPrefixOf` name l

> mkLabelIdent :: String -> Ident
> mkLabelIdent c = renameIdent (mkIdent c) (-1)

> renameLabel :: Ident -> Ident
> renameLabel l = renameIdent l (-1)


> fpSelExt = "_#selFP"
> recSelExt = "_#selR@"
> recUpdExt = "_#updR@"
> recordExt = "_#Rec:"
> labelExt = "_#Lab:"


> instance SrcRefOf Ident where
>     srcRefOf = srcRefOf . positionOfIdent

> instance SrcRefOf QualIdent where
>     srcRefOf = srcRefOf . unqualify

> updIdentName :: (String -> String) -> Ident -> Ident
> updIdentName f ident = let p=positionOfIdent ident
>                            i=uniqueId ident
>                            n=name ident in
>   addPositionIdent p $ flip renameIdent i $ mkIdent (f n)
