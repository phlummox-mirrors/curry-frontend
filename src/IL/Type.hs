{- |
    Module      :  $Header$
    Description :  Definition of the intermediate language (IL)
    Copyright   :  (c) 1999 - 2003 Wolfgang Lux
                                   Martin Engelke
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

   The module 'IL' defines the intermediate language which will be
   compiled into abstract machine code. The intermediate language removes
   a lot of syntactic sugar from the Curry source language.  Top-level
   declarations are restricted to data type and function definitions. A
   newtype definition serves mainly as a hint to the backend that it must
   provide an auxiliary function for partial applications of the
   constructor (Newtype constructors must not occur in patterns
   and may be used in expressions only as partial applications.).

   Type declarations use a de-Bruijn indexing scheme (starting at 0) for
   type variables. In the type of a function, all type variables are
   numbered in the order of their occurence from left to right, i.e., a
   type '(Int -> b) -> (a,b) -> c -> (a,c)' is translated into the
   type (using integer numbers to denote the type variables)
   '(Int -> 0) -> (1,0) -> 2 -> (1,2)'.

   Pattern matching in an equation is handled via flexible and rigid
   'Case' expressions. Overlapping rules are translated with the
   help of 'Or' expressions. The intermediate language has three
   kinds of binding expressions, 'Exist' expressions introduce a
   new logical variable, 'Let' expression support a single
   non-recursive variable binding, and 'Letrec' expressions
   introduce multiple variables with recursive initializer expressions.
   The intermediate language explicitly distinguishes (local) variables
   and (global) functions in expressions.

   Note: this modified version uses haskell type 'Integer'
   instead of 'Int' for representing integer values. This provides
   an unlimited range of integer constants in Curry programs.
-}

{-# LANGUAGE DeriveDataTypeable #-}

module IL.Type
  ( -- * Data types
    Module (..), Decl (..), ConstrDecl (..), CallConv (..), Type (..)
  , Literal (..), ConstrTerm (..), Expression (..), Eval (..), Alt (..)
  , Binding (..)
  ) where

import Data.Generics       (Data, Typeable)

import Curry.Base.Ident
import Curry.Base.Position (SrcRef(..), SrcRefOf (..))

import Base.Expr

data Module = Module ModuleIdent [ModuleIdent] [Decl]
    deriving (Eq, Show, Data, Typeable)

data Decl
  = DataDecl     QualIdent Int [ConstrDecl [Type]]
  | NewtypeDecl  QualIdent Int (ConstrDecl Type)
  | FunctionDecl QualIdent [Ident] Type Expression
  | ExternalDecl QualIdent CallConv String Type
    deriving (Eq, Show, Data, Typeable)

data ConstrDecl a = ConstrDecl QualIdent a
    deriving (Eq, Show, Data, Typeable)

data CallConv
  = Primitive
  | CCall
    deriving (Eq, Show, Data, Typeable)

data Type
  = TypeConstructor QualIdent [Type]
  | TypeVariable    Int
  | TypeArrow       Type Type
    deriving (Eq, Show, Data, Typeable)

data Literal
  = Char  SrcRef Char
  | Int   SrcRef Integer
  | Float SrcRef Double
    deriving (Eq, Show, Data, Typeable)

data ConstrTerm
    -- |literal patterns
  = LiteralPattern Literal
    -- |constructors
  | ConstructorPattern QualIdent [Ident]
    -- |default
  | VariablePattern Ident
  deriving (Eq, Show, Data, Typeable)

data Expression
    -- |literal constants
  = Literal Literal
    -- |variables
  | Variable Ident
    -- |functions
  | Function QualIdent Int
    -- |constructors
  | Constructor QualIdent Int
    -- |applications
  | Apply Expression Expression
    -- |case expressions
  | Case SrcRef Eval Expression [Alt]
    -- |non-deterministic or
  | Or Expression Expression
    -- |exist binding (introduction of a free variable)
  | Exist Ident Expression
    -- |let binding
  | Let Binding Expression
    -- |letrec binding
  | Letrec [Binding] Expression
    -- |typed expression
  | Typed Expression Type
  deriving (Eq, Show, Data, Typeable)

data Eval
  = Rigid
  | Flex
    deriving (Eq, Show, Data, Typeable)

data Alt = Alt ConstrTerm Expression
    deriving (Eq, Show, Data, Typeable)

data Binding = Binding Ident Expression
    deriving (Eq, Show, Data, Typeable)

instance Expr Expression where
  fv (Variable            v) = [v]
  fv (Apply           e1 e2) = fv e1 ++ fv e2
  fv (Case       _ _ e alts) = fv e  ++ fv alts
  fv (Or              e1 e2) = fv e1 ++ fv e2
  fv (Exist             v e) = filter (/= v) (fv e)
  fv (Let (Binding v e1) e2) = fv e1 ++ filter (/= v) (fv e2)
  fv (Letrec          bds e) = filter (`notElem` vs) (fv es ++ fv e)
    where (vs, es) = unzip [(v, e') | Binding v e' <- bds]
  fv _                       = []

instance Expr Alt where
  fv (Alt (ConstructorPattern _ vs) e) = filter (`notElem` vs) (fv e)
  fv (Alt (VariablePattern       v) e) = filter (v /=) (fv e)
  fv (Alt _                         e) = fv e

instance SrcRefOf ConstrTerm where
  srcRefOf (LiteralPattern       l) = srcRefOf l
  srcRefOf (ConstructorPattern i _) = srcRefOf i
  srcRefOf (VariablePattern      i) = srcRefOf i

instance SrcRefOf Literal where
  srcRefOf (Char  s _) = s
  srcRefOf (Int   s _) = s
  srcRefOf (Float s _) = s
