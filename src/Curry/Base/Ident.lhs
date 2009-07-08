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

> module Curry.Base.Ident(Ident(..), showIdent,
>                         QualIdent(..),ModuleIdent(..),SrcRefOf(..),
>                         mkIdent, qualName,
>                         renameIdent, unRenameIdent,
>                         mkMIdent, moduleName,
>                         isInfixOp, isQInfixOp,
>                         qualify, qualifyWith, qualQualify,
>                         isQualified, unqualify, qualUnqualify,
>                         localIdent, -- splitQualIdent,
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
>                         recordExt, labelExt, mkLabelIdent,-- hasPositionIdent,
>                         addPositionIdent, 
>                         addPositionModuleIdent,addRef,addRefId,
>                         positionOfQualIdent,updQualIdent ) where

> import Control.Monad(liftM)
> import Data.Char
> import Data.List
> import Data.Maybe
> import Data.Generics
> import Data.Function(on)

> import Curry.Base.Position


Simple identifiers

> data Ident = Ident { positionOfIdent :: Position,
>                      name :: String,
>                      uniqueId :: Int }
>              deriving (Read, Show, Data, Typeable)
>
> instance Eq Ident where
>     Ident _ m i == Ident _ n j = (m,i) == (n, j)
>
> instance Ord Ident where
>     Ident _ m i `compare` Ident _ n j = (m,i) `compare` (n, j)
>
> showIdent :: Ident -> String
> showIdent  (Ident _ x 0) = x
> showIdent  (Ident _ x n) = x ++ '.' : show n


Qualified identifiers

> data QualIdent = QualIdent { qualidMod :: Maybe ModuleIdent,
>                              qualidId:: Ident }
>                  deriving (Eq, Ord, Read, Show, Data,Typeable)

> qualName :: QualIdent -> String
> qualName (QualIdent Nothing x) = name x
> qualName (QualIdent (Just m) x) = moduleName m ++ "." ++ name x


Module names

> data ModuleIdent = ModuleIdent { positionOfModuleIdent :: Position,
>                                  moduleQualifiers :: [String] }
>                    deriving (Read, Show, Data,Typeable)

> instance Eq ModuleIdent where
>    (==) = (==) `on` moduleQualifiers

> instance Ord ModuleIdent where
>    compare = compare `on` moduleQualifiers

> moduleName :: ModuleIdent -> String
> moduleName = concat . intersperse "." . moduleQualifiers


-- -----------------------------------------

> addPositionIdent :: Position -> Ident -> Ident
> addPositionIdent pos (Ident NoPos x n) = Ident pos x n
> addPositionIdent AST{ast=sr} (Ident pos x n)
>     =  Ident pos{ast=sr} x n
> addPositionIdent pos (Ident _ x n) = Ident pos x n

> addPositionModuleIdent :: Position -> ModuleIdent -> ModuleIdent
> addPositionModuleIdent pos (ModuleIdent _ x) = ModuleIdent pos x 

> positionOfQualIdent :: QualIdent -> Position
> positionOfQualIdent = positionOfIdent . qualidId

> mkIdent :: String -> Ident
> mkIdent x = Ident NoPos x 0

> renameIdent :: Ident -> Int -> Ident
> renameIdent (Ident p x _) n = Ident p x n


> unRenameIdent :: Ident -> Ident
> unRenameIdent (Ident p x _) = Ident p x 0

> mkMIdent :: [String] -> ModuleIdent
> mkMIdent = ModuleIdent NoPos

> isInfixOp :: Ident -> Bool
> isInfixOp (Ident _ ('<':c:cs) _)=
>   last (c:cs) /= '>' || not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident _ (c:_) _) = not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident _ _ _) = False -- error "Zero-length identifier"

> isQInfixOp :: QualIdent -> Bool
> isQInfixOp (QualIdent _ x) = isInfixOp x

\end{verbatim}
The functions \texttt{qualify} and \texttt{qualifyWith} convert an
unqualified identifier into a qualified identifier (without and with a
given module prefix, respectively).
\begin{verbatim}

> qualify :: Ident -> QualIdent
> qualify = QualIdent Nothing

> qualifyWith :: ModuleIdent -> Ident -> QualIdent
> qualifyWith = QualIdent . Just

> qualQualify :: ModuleIdent -> QualIdent -> QualIdent
> qualQualify m (QualIdent Nothing x) = QualIdent (Just m) x
> qualQualify _ x = x

> isQualified :: QualIdent -> Bool
> isQualified (QualIdent m _) = isJust m

> unqualify :: QualIdent -> Ident
> unqualify (QualIdent _ x) = x

> qualUnqualify :: ModuleIdent -> QualIdent -> QualIdent
> qualUnqualify m qid@(QualIdent Nothing x) = qid
> qualUnqualify m (QualIdent (Just m') x) = QualIdent m'' x
>     where m'' | m == m' = Nothing
>               | otherwise    = Just m'

> localIdent :: ModuleIdent -> QualIdent -> Maybe Ident
> localIdent _ (QualIdent Nothing x) = Just x
> localIdent m (QualIdent (Just m') x)
>   | m == m' = Just x
>   | otherwise = Nothing

> splitQualIdent :: QualIdent -> (Maybe ModuleIdent,Ident)
> splitQualIdent (QualIdent m x) = (m,x)

> updQualIdent :: (ModuleIdent -> ModuleIdent) -> (Ident -> Ident) -> QualIdent -> QualIdent
> updQualIdent f g (QualIdent m x) = QualIdent (liftM f m) (g x)

> addRef :: SrcRef -> QualIdent -> QualIdent
> addRef r = updQualIdent id (addRefId r)

> addRefId :: SrcRef -> Ident -> Ident
> addRefId = addPositionIdent . AST

\end{verbatim}
A few identifiers a predefined here.
\begin{verbatim}

> emptyMIdent, mainMIdent, preludeMIdent :: ModuleIdent
> emptyMIdent   = ModuleIdent NoPos []
> mainMIdent    = ModuleIdent NoPos ["main"]
> preludeMIdent = ModuleIdent NoPos ["Prelude"]

> anonId :: Ident
> anonId = Ident NoPos "_" 0

> unitId, boolId, charId, intId, floatId, listId, ioId, successId :: Ident
> unitId    = Ident NoPos "()" 0
> boolId    = Ident NoPos "Bool" 0
> charId    = Ident NoPos "Char" 0
> intId     = Ident NoPos "Int" 0
> floatId   = Ident NoPos "Float" 0
> listId    = Ident NoPos "[]" 0
> ioId      = Ident NoPos "IO" 0
> successId = Ident NoPos "Success" 0

> trueId, falseId, nilId, consId :: Ident
> trueId  = Ident NoPos "True" 0
> falseId = Ident NoPos "False" 0
> nilId   = Ident NoPos "[]" 0
> consId  = Ident NoPos ":" 0

> tupleId :: Int -> Ident
> tupleId n
>   | n >= 2 = Ident NoPos ("(" ++ replicate (n - 1) ',' ++ ")") 0
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
> mainId = Ident NoPos "main" 0
> minusId = Ident NoPos "-" 0
> fminusId = Ident NoPos "-." 0

> qUnitId, qNilId, qConsId, qListId :: QualIdent
> qUnitId = QualIdent Nothing unitId
> qListId = QualIdent Nothing listId
> qNilId  = QualIdent Nothing nilId
> qConsId = QualIdent Nothing consId

> qBoolId, qCharId, qIntId, qFloatId, qSuccessId, qIOId :: QualIdent
> qBoolId = QualIdent (Just preludeMIdent) boolId
> qCharId = QualIdent (Just preludeMIdent) charId
> qIntId = QualIdent (Just preludeMIdent) intId
> qFloatId = QualIdent (Just preludeMIdent) floatId
> qSuccessId = QualIdent (Just preludeMIdent) successId
> qIOId = QualIdent (Just preludeMIdent) ioId

> qTrueId, qFalseId :: QualIdent
> qTrueId = QualIdent (Just preludeMIdent) trueId
> qFalseId = QualIdent (Just preludeMIdent) falseId

> qTupleId :: Int -> QualIdent
> qTupleId = QualIdent Nothing . tupleId

> isQTupleId :: QualIdent -> Bool
> isQTupleId = isTupleId . unqualify

> qTupleArity :: QualIdent -> Int
> qTupleArity = tupleArity . unqualify

\end{verbatim}
Micellaneous function for generating and testing extended identifiers.
\begin{verbatim}

> fpSelectorId :: Int -> Ident
> fpSelectorId n = Ident NoPos (fpSelExt ++ show n) 0

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
