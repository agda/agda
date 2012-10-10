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
import Test.QuickCheck

import Agda.Syntax.Common
import Agda.Syntax.Abstract.Name

import Agda.Utils.Monad
import Agda.Utils.Impossible
#include "../../undefined.h"

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
    { splitArg   :: Int           -- ^ Arg. no to split at.
    , splitTrees :: SplitTrees' a -- ^ Sub split trees.
    }
    deriving (Eq)

-- | Split tree branching.  A finite map from constructor names to splittrees
--   A list representation seems appropriate, since we are expecting not
--   so many constructors per data type, and there is no need for
--   random access.
type SplitTrees' a = [(a, SplitTree' a)]

-- * Printing a split tree

data SplitTreeLabel a = SplitTreeLabel
  { lblConstructorName :: Maybe a   -- ^ 'Nothing' for root of split tree
  , lblSplitArg        :: Maybe Int
  , lblBindings        :: Maybe Int
  }
instance Show a => Show (SplitTreeLabel a) where
  show (SplitTreeLabel Nothing Nothing (Just n))  = "done, " ++ show n ++ " bindings"
  show (SplitTreeLabel Nothing (Just n) Nothing)  = "split at " ++ show n
  show (SplitTreeLabel (Just q) Nothing (Just n)) = show q ++ " -> done, " ++ show n ++ " bindings"
  show (SplitTreeLabel (Just q) (Just n) Nothing) = show q ++ " -> split at " ++ show n
  show _ = __IMPOSSIBLE__

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

instance Show a => Show (SplitTree' a) where
  show = drawTree . fmap show . toTree

-- * Generating random split trees for testing

instance Arbitrary a => Arbitrary (SplitTree' a) where
  arbitrary = frequency
    [ (5, return $ SplittingDone 0)
    , (3, SplitAt <$> choose (1,5) <*> (take 3 <$> listOf1 arbitrary))
    ]

-- * Testing the printer

newtype CName = CName String
instance Show CName where
  show (CName s) = s

instance Arbitrary CName where
  arbitrary = CName <$> elements
    [ "zero", "suc", "nil", "cons", "left", "right", "just", "nothing" ]

testSplitTreePrinting = sample (arbitrary :: Gen (SplitTree' CName))
