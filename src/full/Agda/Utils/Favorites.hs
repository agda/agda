{-# LANGUAGE CPP, NoImplicitPrelude, DeriveFoldable #-}

-- | Maintaining a list of favorites of some partially ordered type.
--   Only the best elements are kept.
--
--   To avoid name clashes, import this module qualified, as in
--   @
--      import Agda.Utils.Favorites (Favorites)
--      import qualified Agda.Utiles.Favorites as Fav
--   @

module Agda.Utils.Favorites where

import Data.Bool
import Data.Function
import qualified Data.List as List

import Data.Foldable (Foldable)

import Agda.Utils.PartialOrd

#include "../undefined.h"
import Agda.Utils.Impossible

-- | A list of incomparable favorites.
newtype Favorites a = Favorites { favorites :: [a] }
  deriving (Foldable)

null :: Favorites a -> Bool
null = List.null . favorites

-- | No favorites yet.  Poor me!
empty :: Favorites a
empty = Favorites []

-- | You are my one and only, darling!
singleton :: a -> Favorites a
singleton a = Favorites [a]

-- | Result of comparing a candidate with the current favorites.
data CompareResult a
  = Dominates   { dominated :: [a], notDominated :: [a] }
    -- ^ Great, you are dominating a possibly (empty list of favorites)
    --   but there is also a rest that is not dominated.
    --   If @null dominated@, then @notDominated@ is necessarily the
    --   complete list of favorites.
  | IsDominated { dominator :: a }
    -- ^ Sorry, but you are dominated by that favorite.


-- | Gosh, got some pretty @a@ here, compare with my current favorites!
--   Discard it if there is already one that is better or equal.
--   (Skewed conservatively: faithful to the old favorites.)
--   If there is no match for it, add it, and
--   dispose of all that are worse than @a@.
--
--   We require a partial ordering.  Less is better! (Maybe paradoxically.)
compareWithFavorites :: PartialOrd a => a -> Favorites a -> CompareResult a
compareWithFavorites a (Favorites as) = loop as where
  loop []          = Dominates [] []
  loop as@(b : bs) = case comparable a b of
    POLT -> dominates b $ loop bs  -- @a@ is a new favorite, bye-bye, @b@
    POLE -> dominates b $ loop bs  -- ditto
    POEQ -> IsDominated a          -- @b@ is as least as good as @a@, bye-bye, @a@
    POGE -> IsDominated a          -- ditto
    POGT -> IsDominated a          -- ditto
    POAny -> doesnotd b $ loop bs -- don't know, compare with my other favorites
  -- add an outperformed favorite
  dominates b (Dominates bs as) = Dominates (b : bs) as
  dominates b (IsDominated a)   = IsDominated a
  -- add an uncomparable favorite
  doesnotd  b (Dominates as bs) = Dominates as (b : bs)
  doesnotd  b (IsDominated a)   = IsDominated a

-- | After comparing, do the actual insertion.
insertCompared :: PartialOrd a => a -> Favorites a -> CompareResult a -> Favorites a
insertCompared a _ (Dominates _ as) = Favorites (a : as)
insertCompared _ l IsDominated{}    = l

-- | Compare, then insert accordingly.
--   @insert a l = insertCompared a l (compareWithFavorites a l)@
insert :: PartialOrd a => a -> Favorites a -> Favorites a
insert a l = insertCompared a l (compareWithFavorites a l)

{-
-- | Gosh, got some pretty @a@ here, compare with my current favorites!
--   Discard it if there is already one that is better or equal.
--   (Skewed conservatively: faithful to the old favorites.)
--   If there is no match for it, add it, and
--   dispose of all that are worse than @a@.
--
--   We require a partial ordering.  Less is better! (Maybe paradoxically.)
insert :: PartialOrd a => a -> Favorites a -> Favorites a
insert a (Favorites as) = Favorites $ loop as where
  loop []          = [a]
  loop as@(b : bs) = case comparable a b of
    POLT -> loop bs      -- @a@ is a new favorite, bye-bye, @b@
    POLE -> loop bs      -- ditto
    POEQ -> as           -- @b@ is as least as good as @a@, bye-bye, @a@
    POGE -> as           -- ditto
    POGT -> as           -- ditto
    POAny -> b : loop bs -- don't know, compare with my other favorites
-}

-- | Insert all the favorites from the first list into the second.
union :: PartialOrd a => Favorites a -> Favorites a -> Favorites a
union (Favorites as) bs = List.foldr insert bs as
