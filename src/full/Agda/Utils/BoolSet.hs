{-# OPTIONS_GHC -Wunused-imports #-}

-- | Representation of @'Set' 'Bool'@ as a 4-element enum type.
--
-- All operations in constant time and space.
--
-- Mimics the interface of 'Data.Set'.
--
-- Import as:
-- @
--    import qualified Agda.Utils.BoolSet as BoolSet
--    import Agda.Utils.BoolSet (BoolSet)
-- @

module Agda.Utils.BoolSet
  ( BoolSet
  , (\\)
  , complement
  , delete
  , difference
  , elems
  , empty
  , fromList, fromAscList, fromDistinctAscList
  , insert
  , intersection
  , isSubsetOf
  , lookupMin
  , member
  , notMember
  , null
  , singleton
  , size
  , toList, toAscList
  , toSingleton
  , total
  , union
  ) where

import Prelude hiding (null)

import Agda.Utils.Impossible

-- | Isomorphic to @'Set' 'Bool'@.
data BoolSet = SetEmpty | SetTrue | SetFalse | SetBoth
  deriving (Eq, Ord, Show, Enum, Bounded)

-- * Query

null :: BoolSet -> Bool
null = (SetEmpty ==)

size :: BoolSet -> Int
size = \case
  SetEmpty -> 0
  SetTrue  -> 1
  SetFalse -> 1
  SetBoth  -> 2

member :: Bool -> BoolSet -> Bool
member b = \case
  SetEmpty -> False
  SetBoth  -> True
  SetTrue  -> b
  SetFalse -> not b

-- | @not . member b@.
notMember :: Bool -> BoolSet -> Bool
notMember b = not . member b

isSubsetOf ::  BoolSet -> BoolSet -> Bool
isSubsetOf = curry $ \case
  (SetEmpty , _        ) -> True
  (_        , SetBoth  ) -> True
  (SetTrue  , SetTrue  ) -> True
  (SetFalse , SetFalse ) -> True
  _                      -> False

lookupMin :: BoolSet -> Maybe Bool
lookupMin = \case
  SetEmpty -> Nothing
  SetTrue  -> Just True
  _        -> Just False

-- | @toSingleton s == Just b@ iff @s == singleton b@.
toSingleton :: BoolSet -> Maybe Bool
toSingleton  = \case
  SetTrue  -> Just True
  SetFalse -> Just False
  _        -> Nothing

-- * Construction

-- | The empty set.
empty :: BoolSet
empty = SetEmpty

-- | The full set.
total :: BoolSet
total = SetBoth

-- | A singleton set.
singleton :: Bool -> BoolSet
singleton = \case
  True  -> SetTrue
  False -> SetFalse

insert :: Bool -> BoolSet -> BoolSet
insert b = \case
  SetBoth  -> SetBoth
  SetEmpty -> singleton b
  SetTrue  -> if b then SetTrue else SetBoth
  SetFalse -> if b then SetBoth else SetFalse

delete :: Bool -> BoolSet -> BoolSet
delete b = \case
  SetEmpty -> SetEmpty
  SetTrue  -> if b then SetEmpty else SetTrue
  SetFalse -> if b then SetFalse else SetEmpty
  SetBoth  -> if b then SetFalse else SetTrue

-- * Combine

complement :: BoolSet -> BoolSet
complement = \case
  SetEmpty -> SetBoth
  SetBoth  -> SetEmpty
  SetTrue  -> SetFalse
  SetFalse -> SetTrue

difference, (\\) :: BoolSet -> BoolSet -> BoolSet
difference = curry $ \case
  (SetEmpty , _        ) -> SetEmpty
  (_        , SetBoth  ) -> SetEmpty
  (s        , SetEmpty ) -> s
  (SetBoth  , SetTrue  ) -> SetFalse
  (SetBoth  , SetFalse ) -> SetTrue
  (SetTrue  , SetTrue  ) -> SetEmpty
  (SetTrue  , SetFalse ) -> SetTrue
  (SetFalse , SetTrue  ) -> SetFalse
  (SetFalse , SetFalse ) -> SetEmpty
(\\)       = difference

intersection ::  BoolSet -> BoolSet -> BoolSet
intersection = curry $ \case
  (SetEmpty , _        ) -> SetEmpty
  (_        , SetEmpty ) -> SetEmpty
  (SetBoth  , s        ) -> s
  (s        , SetBoth  ) -> s
  (SetTrue  , SetTrue  ) -> SetTrue
  (SetFalse , SetTrue  ) -> SetEmpty
  (SetTrue  , SetFalse ) -> SetEmpty
  (SetFalse , SetFalse ) -> SetFalse

union ::  BoolSet -> BoolSet -> BoolSet
union = curry $ \case
  (SetBoth  , _        ) -> SetBoth
  (_        , SetBoth  ) -> SetBoth
  (SetEmpty , s        ) -> s
  (s        , SetEmpty ) -> s
  (SetTrue  , SetTrue  ) -> SetTrue
  (SetFalse , SetTrue  ) -> SetBoth
  (SetTrue  , SetFalse ) -> SetBoth
  (SetFalse , SetFalse ) -> SetFalse

-- * Conversion

elems, toList, toAscList :: BoolSet -> [Bool]
elems     = \case
  SetEmpty -> []
  SetTrue  -> [True]
  SetFalse -> [False]
  SetBoth  -> [False, True]
toList    = elems
toAscList = elems

fromList, fromAscList, fromDistinctAscList :: [Bool] -> BoolSet
fromList            = foldr insert SetEmpty
fromAscList         = fromList
fromDistinctAscList = \case
  []            -> SetEmpty
  [False]       -> SetFalse
  [True]        -> SetTrue
  [False, True] -> SetBoth
  _             -> __IMPOSSIBLE__
