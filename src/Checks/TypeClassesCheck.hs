{- |
    Module      :  $Header$
    Description :  
    Copyright   :  (c) 2013 Matthias Böhm
    License     :  OtherLicense

    Maintainer  :  bjp@informatik.uni-kiel.de
    Stability   :  experimental
    Portability :  portable

    Description: TODO
-}

module Checks.TypeClassesCheck (typeClassesCheck) where

import Curry.Syntax.Type
import Env.ClassEnv
import Base.Messages (Message, posMessage, internalError)

typeClassesCheck :: [Decl] -> ([Decl], ClassEnv, [Message])
typeClassesCheck decls = (decls, initClassEnv, [])

