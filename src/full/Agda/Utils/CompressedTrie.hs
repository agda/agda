{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wunused-matches #-}
{-# OPTIONS_GHC -Wunused-binds #-}

-- | Strict compressed tries
--   (based on "Data.Map.Strict" and "Agda.Utils.Maybe.Strict").
--
-- In contrast to "Agda.Utils.Trie", branches from a node
-- can be labeled with non-empty lists of keys that do not
-- overlap, meaning they start with different first elements.
-- This way, non-branching unlabelled pathes can be stored
-- more efficiently.
--
-- As a side effect, the notion of height changes
-- which we utilize in the 'truncate' function.
--
-- An 'Agda.Utils.CompressedTrie.Trie' is usually constructed
-- from an 'Agda.Utils.Trie.Trie' via the 'compress' function.

module Agda.Utils.CompressedTrie where

import Prelude hiding (null, truncate)

import Control.DeepSeq

import Data.Map.Strict         (Map)
import Data.Map.Strict         qualified as Map
import Data.Monoid             (Sum(Sum,getSum))

import Agda.Utils.List1        (List1, pattern (:|))
import Agda.Utils.List1        qualified as List1
import Agda.Utils.Map          (isSingleMap)
import Agda.Utils.Maybe.Strict qualified as Strict
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Trie         qualified as Uncompressed

import Agda.Utils.Impossible (__IMPOSSIBLE__)

-- | Finite map from @[k]@ to @v@.
--
--   With the strict 'Maybe' type, 'Trie' is also strict in 'v'.
--
--   Invariant: only the root of the tree
--   may be of the form @Trie Nothing (Map.singleton ks t)@.
--   A node inside of the trie of that form must be fused
--   into its branch.
data Trie k v = Trie
  { trieValue    :: !(Strict.Maybe v)
  , trieBranches :: !(Map (List1 k) (Trie k v))
      -- Invariant: The keys are prefix-free, meaning their first letters differ.
  }
  deriving
    ( Show
    , Eq
        -- Andreas, 2024-11-16: The derived Eq isn't extensional.
        -- It disguishes different representation of the empty Trie.
        -- (E.g. the empty map and the map that only contains Nothing values.)
    , Functor
    , Foldable
    )

instance (NFData k, NFData v) => NFData (Trie k v) where
  rnf (Trie a b) = rnf a `seq` rnf b

---------------------------------------------------------------------------
-- * Construction

-- | Empty trie.
instance Null (Trie k v) where
  empty = Trie Strict.Nothing Map.empty
  null (Trie v t) = null v && all null t
    -- Andreas, 2024-11-16: since we allow non-canoncial tries,
    -- we have to check that every subtrie is empty,
    -- not just that there are no subtries.

-- | Singleton tree with value at the root.
root :: v -> Trie k v
root v = Trie (Strict.Just v) Map.empty

instance Singleton ([k],v) (Trie k v) where
  singleton = uncurry Agda.Utils.CompressedTrie.singleton

-- | Singleton trie.
singleton :: [k] -> v -> Trie k v
singleton []       = root
singleton (k : ks) = singleton1 (k :| ks)

-- | Singleton tree with empty root.
singleton1 :: List1 k -> v -> Trie k v
singleton1 ks = Trie Strict.Nothing . Map.singleton ks . root

-- | A single branch with the given subtree.
--   Precondition: the given subtree has a value at the root.
singleBranch :: List1 k -> Trie k v -> (List1 k, Trie k v)
singleBranch ks t
  | Just (ks', t') <- isSingleBranch t = (ks <> ks', t')
  | otherwise = (ks, t)

-- | Is the trie starting with a single branch?
isSingleBranch :: Trie k v -> Maybe (List1 k, Trie k v)
isSingleBranch = \case
  Trie Strict.Nothing ts | Just (k, t) <- isSingleMap ts
    -> Just (k, t)
  _ -> Nothing

-- | Turn a trie into a compressed trie.
compress :: Ord k => Uncompressed.Trie k v -> Trie k v
compress (Uncompressed.Trie mv ts) =
    Trie mv $ Map.fromList $ map go $ Map.toList ts
  where
    go (k, t) = singleBranch (List1.singleton k) (compress t)

---------------------------------------------------------------------------
-- * Deconstruction

-- | Turn a compressed trie into an uncompressed trie.
uncompress :: forall k v. Ord k => Trie k v -> Uncompressed.Trie k v
uncompress (Trie mv ts) =
    Uncompressed.Trie mv $ Map.fromList $ map go $ Map.toList ts
  where
    go :: (List1 k, Trie k v) -> (k, Uncompressed.Trie k v)
    go (k :| ks, t) = (k, Uncompressed.prefixBy ks $ uncompress t)

-- | Convert to ascending list.
toList :: Ord k => Trie k v -> [([k],v)]
toList = toAscList

-- | Convert to ascending list.
toAscList :: Ord k => Trie k v -> [([k],v)]
toAscList (Trie mv ts) = Strict.maybeToList (([],) <$> mv) ++
  [ (List1.toList ks1 ++ ks, v)
  | (ks1, t) <- Map.toAscList ts
  , (ks,  v) <- toAscList t
  ]

-- | The number of labeled nodes.
size :: Trie k v -> Int
size (Trie mv ts) = Strict.maybe 0 (const 1) mv + getSum (foldMap (Sum . size) ts)

-- | The number of nodes that are labeled or leaves..
sizeWithLeaves :: Trie k v -> Int
sizeWithLeaves (Trie mv ts)
  | null ts   = 1
  | otherwise = Strict.maybe 0 (const 1) mv + getSum (foldMap (Sum . sizeWithLeaves) ts)

---------------------------------------------------------------------------
-- * Modification

-- | Modify the leaves (input and output may be non-canonical).

substLeaves :: (Maybe v -> Trie k v) -> Trie k v -> Trie k v
substLeaves f (Trie mv ts)
  | null ts   = f $ Strict.toLazy mv
  | otherwise = Trie mv (fmap (substLeaves f) ts)

-- | Truncate tree at given depth.
--   @truncate 0 t@ returns the root.

truncate :: Int -> Trie k v -> Trie k v
truncate n t@(Trie mv ts)
  | n <= 0    = if null ts then t else empty
  | otherwise = Trie mv $ fmap (truncate (n - 1)) ts

-- | Truncate the tree so that it has at most the given size
--   according to the given sizing function.
--   @truncateSize sizing 0 t@ returns the trie @truncate 0 t@.

truncateSize :: forall k v. (Trie k v -> Int) -> Int -> Trie k v -> Trie k v
truncateSize size n t =
  -- Drop while still increasing but staying below n.
  case
    dropWhile
      (\ ((n1,_),(n2,_)) -> n1 < n2 && n2 < n)
      (zip ts (drop 1 ts))
  of
  -- Return the last trie that was still increasing and stayed below n.
    ((_, t1), _) : _ -> t1
    [] -> __IMPOSSIBLE__
  where
    ts :: [(Int, Trie k v)]
    ts = [ (size t', t') | d <- [0..], let t' = truncate d t ]

-- | @truncateSize sizeWithLeaves@
truncateSizeWithLeaves :: Int -> Trie k v -> Trie k v
truncateSizeWithLeaves = truncateSize sizeWithLeaves
