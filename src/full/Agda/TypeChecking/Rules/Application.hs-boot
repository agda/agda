{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rules.Application where

import Data.List.NonEmpty (NonEmpty)

import Agda.Syntax.Common (ProjOrigin)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

checkArguments ::
     Comparison
  -> ExpandHidden
  -> A.Expr
  -> A.ArgsWithInfo
  -> Type
  -> Type
  -> (ArgsCheckState CheckedTarget -> TCM Term)
  -> TCM Term

checkArguments_ ::
     Comparison
  -> ExpandHidden
  -> A.Expr
  -> A.ArgsWithInfo
  -> Telescope
  -> TCM (Elims, Telescope)

checkApplication :: Comparison -> A.Expr -> A.ArgsWithInfo -> A.Expr -> Type -> TCM Term

inferApplication :: ExpandHidden -> A.Expr -> A.ArgsWithInfo -> A.Expr -> TCM (Term, Type)

checkProjAppToKnownPrincipalArg ::
     Comparison
  -> A.Expr
  -> ProjOrigin
  -> NonEmpty QName
  -> A.Expr
  -> A.ArgsWithInfo
  -> Type
  -> Int
  -> Term
  -> Type
  -> PrincipalArgTypeMetas
  -> TCM Term

disambiguateConstructor' :: ConstructorDisambiguationData -> (ConHead -> TCM Term) -> TCM Term

univChecks :: Univ -> TCM ()

suffixToLevel :: Suffix -> Integer
