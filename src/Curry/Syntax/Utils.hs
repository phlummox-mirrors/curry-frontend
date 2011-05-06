module Curry.Syntax.Utils
  ( isEvalAnnot, isTypeSig, infixOp, isTypeDecl, isValueDecl, isInfixDecl
  , isRecordDecl, isImportDecl
  ) where

import Curry.Syntax.Type

isImportDecl :: Decl -> Bool
isImportDecl (ImportDecl _ _ _ _ _) = True
isImportDecl _ = False

isInfixDecl :: Decl -> Bool
isInfixDecl (InfixDecl _ _ _ _) = True
isInfixDecl _ = False

isTypeDecl :: Decl -> Bool
isTypeDecl (DataDecl    _ _ _ _) = True
isTypeDecl (NewtypeDecl _ _ _ _) = True
isTypeDecl (TypeDecl    _ _ _ _) = True
isTypeDecl _                     = False

isTypeSig :: Decl -> Bool
isTypeSig (TypeSig _ _ _)          = True
isTypeSig (ExternalDecl _ _ _ _ _) = True
isTypeSig _                        = False

isEvalAnnot :: Decl -> Bool
isEvalAnnot (EvalAnnot _ _ _) = True
isEvalAnnot _ = False

isValueDecl :: Decl -> Bool
isValueDecl (FunctionDecl _ _ _) = True
isValueDecl (ExternalDecl _ _ _ _ _) = True
isValueDecl (FlatExternalDecl _ _) = True
isValueDecl (PatternDecl _ _ _) = True
isValueDecl (ExtraVariables _ _) = True
isValueDecl _ = False

isRecordDecl :: Decl -> Bool
isRecordDecl (TypeDecl _ _ _ (RecordType _ _)) = True
isRecordDecl _ = False

-- |Convert an infix operator into an expression
infixOp :: InfixOp -> Expression
infixOp (InfixOp op) = Variable op
infixOp (InfixConstr op) = Constructor op
