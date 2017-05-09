{-# LANGUAGE CPP                #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- | Case trees.
--
--   After coverage checking, pattern matching is translated
--   to case trees, i.e., a tree of successive case splits
--   on one variable at a time.

module Agda.TypeChecking.CompiledClause where

import Prelude hiding (null)

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend, Any(..))
import Data.Typeable (Typeable)
import Data.Foldable (Foldable, foldMap)
import Data.Traversable (Traversable, traverse)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Literal
import Agda.Syntax.Position

import Agda.Utils.Null
import Agda.Utils.Pretty hiding ((<>))

#include "undefined.h"
import Agda.Utils.Impossible

data WithArity c = WithArity { arity :: Int, content :: c }
  deriving (Typeable, Functor, Foldable, Traversable)

-- | Branches in a case tree.

data Case c = Branches
  { projPatterns   :: Bool
    -- ^ We are constructing a record here (copatterns).
    --   'conBranches' lists projections.
  , conBranches    :: Map QName (WithArity c)
    -- ^ Map from constructor (or projection) names to their arity
    --   and the case subtree.  (Projections have arity 0.)
  , litBranches    :: Map Literal c
    -- ^ Map from literal to case subtree.
  , catchAllBranch :: Maybe c
    -- ^ (Possibly additional) catch-all clause.
  }
  deriving (Typeable, Functor, Foldable, Traversable)

-- | Case tree with bodies.

data CompiledClauses' a
  = Case (Arg Int) (Case (CompiledClauses' a))
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
    -- If the @n@-th argument is a projection, we have only 'conBranches'
    -- with arity 0.
  | Done [Arg ArgName] a
    -- ^ @Done xs b@ stands for the body @b@ where the @xs@ contains hiding
    --   and name suggestions for the free variables. This is needed to build
    --   lambdas on the right hand side for partial applications which can
    --   still reduce.
  | Fail
    -- ^ Absurd case.
  deriving (Typeable, Functor, Traversable, Foldable)

type CompiledClauses = CompiledClauses' Term

litCase :: Literal -> c -> Case c
litCase l x = Branches False Map.empty (Map.singleton l x) Nothing

conCase :: QName -> WithArity c -> Case c
conCase c x = Branches False (Map.singleton c x) Map.empty Nothing

projCase :: QName -> c -> Case c
projCase c x = Branches True (Map.singleton c $ WithArity 0 x) Map.empty Nothing

catchAll :: c -> Case c
catchAll x = Branches False Map.empty Map.empty (Just x)

-- | Check whether a case tree has a catch-all clause.
hasCatchAll :: CompiledClauses -> Bool
hasCatchAll = getAny . loop
  where
  loop cc = case cc of
    Fail{}    -> mempty
    Done{}    -> mempty
    Case _ br -> maybe (foldMap loop br) (const $ Any True) $ catchAllBranch br

instance Semigroup c => Semigroup (WithArity c) where
  WithArity n1 c1 <> WithArity n2 c2
    | n1 == n2  = WithArity n1 (c1 <> c2)
    | otherwise = __IMPOSSIBLE__   -- arity must match!

instance (Semigroup c, Monoid c) => Monoid (WithArity c) where
  mempty  = WithArity __IMPOSSIBLE__ mempty
  mappend = (<>)

instance Semigroup m => Semigroup (Case m) where
  Branches cop  cs  ls  m <> Branches cop' cs' ls' m' =
    Branches (cop || cop') -- for @projCase <> mempty@
             (Map.unionWith (<>) cs cs')
             (Map.unionWith (<>) ls ls')
             (m <> m')

instance (Semigroup m, Monoid m) => Monoid (Case m) where
  mempty  = empty
  mappend = (<>)

instance Null (Case m) where
  empty = Branches False Map.empty Map.empty Nothing
  null (Branches _cop cs ls mcatch) = null cs && null ls && null mcatch

-- * Pretty instances.

instance Pretty a => Show (Case a) where
  show = show . pretty

instance Show CompiledClauses where
  show = show . pretty

instance Pretty a => Pretty (WithArity a) where
  pretty = pretty . content

instance Pretty a => Pretty (Case a) where
  prettyPrec p (Branches _cop cs ls m) =
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
  pretty (Done hs t) = text ("done" ++ show hs) <+> pretty t
  pretty Fail        = text "fail"
  pretty (Case n bs) | projPatterns bs =
    sep [ text "record"
        , nest 2 $ pretty bs
        ]
  pretty (Case n bs) =
    sep [ text ("case " ++ show n ++ " of")
        , nest 2 $ pretty bs
        ]

-- * KillRange instances.

instance KillRange c => KillRange (WithArity c) where
  killRange = fmap killRange

instance KillRange c => KillRange (Case c) where
  killRange (Branches cop con lit all) = Branches cop
    (killRangeMap con)
    (killRangeMap lit)
    (killRange all)

instance KillRange CompiledClauses where
  killRange (Case i br) = killRange2 Case i br
  killRange (Done xs v) = killRange2 Done xs v
  killRange Fail        = Fail

-- * TermLike instances

instance TermLike a => TermLike (WithArity a) where
  traverseTerm  = fmap . traverseTerm
  traverseTermM = traverse . traverseTermM
  foldTerm      = foldMap . foldTerm

instance TermLike a => TermLike (Case a) where
  traverseTerm  = fmap . traverseTerm
  traverseTermM = traverse . traverseTermM
  foldTerm      = foldMap . foldTerm

instance TermLike a => TermLike (CompiledClauses' a) where
  traverseTerm  = fmap . traverseTerm
  traverseTermM = traverse . traverseTermM
  foldTerm      = foldMap . foldTerm

