{-# LANGUAGE TypeOperators, CPP, DeriveDataTypeable, DeriveFunctor #-}
module Agda.TypeChecking.CompiledClause where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid
import Data.Typeable (Typeable)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal
import Agda.Utils.Pretty

type key :-> value = Map key value

data Case c = Branches { conBranches    :: QName   :-> c
                       , litBranches    :: Literal :-> c
                       , catchAllBranch :: Maybe c
                       }
  deriving (Typeable, Functor)

data CompiledClauses
  = Case Int (Case CompiledClauses)
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
  | Done [Arg String] Term
    -- ^ @Done xs b@ stands for the body @b@ where the @xs@ contains hiding
    --   and name suggestions for the free variables. This is needed to build
    --   lambdas on the right hand side for partial applications which can
    --   still reduce.
  | Fail
    -- ^ Absurd case.
  deriving (Typeable)

litCase l x = Branches Map.empty (Map.singleton l x) Nothing
conCase c x = Branches (Map.singleton c x) Map.empty Nothing
catchAll x  = Branches Map.empty Map.empty (Just x)

instance Monoid m => Monoid (Case m) where
  mempty = Branches Map.empty Map.empty Nothing
  mappend (Branches cs  ls  m)
          (Branches cs' ls' m') =
    Branches (Map.unionWith mappend cs cs')
             (Map.unionWith mappend ls ls')
             (mappend m m')

instance Pretty a => Show (Case a) where
  show = show . pretty
instance Show CompiledClauses where
  show = show . pretty

instance Pretty a => Pretty (Case a) where
  prettyPrec p (Branches cs ls m) =
    mparens (p > 0) $ vcat $
      pr cs ++ pr ls ++ prC m
    where
      prC Nothing = []
      prC (Just x) = [text "_ ->" <+> pretty x]
      pr m = [ sep [ text (show x ++ " ->")
                   , nest 2 $ pretty v ]
             | (x, v) <- Map.toList m ]

instance Pretty CompiledClauses where
  pretty (Done hs t)  = text ("done" ++ show hs) <+> text (show t)
  pretty Fail        = text "fail"
  pretty (Case n bs) =
    sep [ text ("case " ++ show n ++ " of")
        , nest 2 $ pretty bs
        ]
