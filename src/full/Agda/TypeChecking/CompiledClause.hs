-- GHC 7.4.2 requires this layout for the pragmas. See Issue 1460.
{-# LANGUAGE CPP,
             DeriveDataTypeable,
             DeriveFoldable,
             DeriveFunctor,
             DeriveTraversable #-}

-- | Case trees.
--
--   After coverage checking, pattern matching is translated
--   to case trees, i.e., a tree of successive case splits
--   on one variable at a time.

module Agda.TypeChecking.CompiledClause where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Monoid
import Data.Typeable (Typeable)
import Data.Foldable (Foldable)
import Data.Traversable (Traversable)

import Agda.Syntax.Internal
import Agda.Syntax.Literal

import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

data WithArity c = WithArity { arity :: Int, content :: c }
  deriving (Typeable, Functor, Foldable, Traversable)

-- | Branches in a case tree.

data Case c = Branches
  { conBranches    :: Map QName (WithArity c)
    -- ^ Map from constructor (or projection) names to their arity
    --   and the case subtree.  (Projections have arity 0.)
  , litBranches    :: Map Literal c
    -- ^ Map from literal to case subtree.
  , catchAllBranch :: Maybe c
    -- ^ (Possibly additional) catch-all clause.
  }
  deriving (Typeable, Functor, Foldable, Traversable)

-- | Case tree with bodies.

data CompiledClauses
  = Case Int (Case CompiledClauses)
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
    -- If the @n@-th argument is a projection, we have only 'conBranches'.
    -- with arity 0.
  | Done [Arg ArgName] Term
    -- ^ @Done xs b@ stands for the body @b@ where the @xs@ contains hiding
    --   and name suggestions for the free variables. This is needed to build
    --   lambdas on the right hand side for partial applications which can
    --   still reduce.
  | Fail
    -- ^ Absurd case.
  deriving (Typeable)

emptyBranches :: Case CompiledClauses
emptyBranches = Branches Map.empty Map.empty Nothing

litCase :: Literal -> c -> Case c
litCase l x = Branches Map.empty (Map.singleton l x) Nothing

conCase :: QName -> WithArity c -> Case c
conCase c x = Branches (Map.singleton c x) Map.empty Nothing

catchAll :: c -> Case c
catchAll x = Branches Map.empty Map.empty (Just x)

instance Monoid c => Monoid (WithArity c) where
  mempty = WithArity __IMPOSSIBLE__ mempty
  mappend (WithArity n1 c1) (WithArity n2 c2)
    | n1 == n2  = WithArity n1 $ mappend c1 c2
    | otherwise = __IMPOSSIBLE__   -- arity must match!

instance Monoid m => Monoid (Case m) where
  mempty = Branches Map.empty Map.empty Nothing
  mappend (Branches cs  ls  m)
          (Branches cs' ls' m') =
    Branches (Map.unionWith mappend cs cs')
             (Map.unionWith mappend ls ls')
             (mappend m m')

-- * Pretty instances.

instance Pretty a => Show (Case a) where
  show = show . pretty

instance Show CompiledClauses where
  show = show . pretty

instance Pretty a => Pretty (WithArity a) where
  pretty = pretty . content

instance Pretty a => Pretty (Case a) where
  prettyPrec p (Branches cs ls m) =
    mparens (p > 0) $ vcat $
      prettyMap cs ++ prettyMap ls ++ prC m
    where
      prC Nothing = []
      prC (Just x) = [text "_ ->" <+> pretty x]

prettyMap :: (Show k, Pretty v) => Map k v -> [Doc]
prettyMap m = [ sep [ text (show x ++ " ->")
                    , nest 2 $ pretty v ]
              | (x, v) <- Map.toList m ]

instance Pretty CompiledClauses where
  pretty (Done hs t) = text ("done" ++ show hs) <+> text (show t)
  pretty Fail        = text "fail"
  pretty (Case n bs) =
    sep [ text ("case " ++ show n ++ " of")
        , nest 2 $ pretty bs
        ]
