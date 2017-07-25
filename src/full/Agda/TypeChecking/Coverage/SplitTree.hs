{-# LANGUAGE CPP #-}

{-| Split tree for transforming pattern clauses into case trees.

The coverage checker generates a split tree from the clauses.
The clause compiler uses it to transform clauses to case trees.

The initial problem is a set of clauses.  The root node designates
on which argument to split and has subtrees for all the constructors.
Splitting continues until there is only a single clause left at
each leaf of the split tree.

-}
module Agda.TypeChecking.Coverage.SplitTree where

import Data.Tree

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal as I

import Agda.Utils.Monad
import Agda.Utils.Pretty

#include "undefined.h"
import Agda.Utils.Impossible

type SplitTree  = SplitTree'  QName
type SplitTrees = SplitTrees' QName

-- | Abstract case tree shape.
data SplitTree' a
  = -- | No more splits coming. We are at a single, all-variable
    -- clause.
    SplittingDone
    { splitBindings :: Int       -- ^  The number of variables bound in the clause
    }
  | -- | A split is necessary.
    SplitAt
    { splitArg   :: Arg Int       -- ^ Arg. no to split at.
    , splitTrees :: SplitTrees' a -- ^ Sub split trees.
    }

-- | Split tree branching.  A finite map from constructor names to splittrees
--   A list representation seems appropriate, since we are expecting not
--   so many constructors per data type, and there is no need for
--   random access.
type SplitTrees' a = [(a, SplitTree' a)]

-- * Printing a split tree

data SplitTreeLabel a = SplitTreeLabel
  { lblConstructorName :: Maybe a   -- ^ 'Nothing' for root of split tree
  , lblSplitArg        :: Maybe (Arg Int)
  , lblBindings        :: Maybe Int
  }
instance Pretty a => Pretty (SplitTreeLabel a) where
  pretty = \case
    SplitTreeLabel Nothing Nothing (Just n)  -> text $ "done, " ++ show n ++ " bindings"
    SplitTreeLabel Nothing (Just n) Nothing  -> text $ "split at " ++ show n
    SplitTreeLabel (Just q) Nothing (Just n) -> pretty q <+> text (" -> done, " ++ show n ++ " bindings")
    SplitTreeLabel (Just q) (Just n) Nothing -> pretty q <+> text (" -> split at " ++ show n)
    _ -> __IMPOSSIBLE__

-- | Convert a split tree into a 'Data.Tree' (for printing).
toTree :: SplitTree' a -> Tree (SplitTreeLabel a)
toTree t = case t of
  SplittingDone n -> Node (SplitTreeLabel Nothing Nothing (Just n)) []
  SplitAt n ts    -> Node (SplitTreeLabel Nothing (Just n) Nothing) $ toTrees ts

toTrees :: SplitTrees' a -> Forest (SplitTreeLabel a)
toTrees = map (\ (c,t) -> setCons c $ toTree t)
  where
    setCons :: a -> Tree (SplitTreeLabel a) -> Tree (SplitTreeLabel a)
    setCons c (Node l ts) = Node (l { lblConstructorName = Just c }) ts

instance Pretty a => Pretty (SplitTree' a) where
  pretty = text . drawTree . fmap prettyShow . toTree
