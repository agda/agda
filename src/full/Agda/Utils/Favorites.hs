{-# OPTIONS_GHC -Wunused-imports #-}

-- | Maintaining a list of favorites of some partially ordered type.
--   Only the best elements are kept.
--
--   To avoid name clashes, import this module qualified, as in
--   @
--      import Agda.Utils.Favorites (Favorites)
--      import qualified Agda.Utils.Favorites as Fav
--   @

module Agda.Utils.Favorites where

import Prelude hiding ( null )

import qualified Data.List as List
import qualified Data.Set as Set

import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.Singleton
import Agda.Utils.Tuple

-- | A list of incomparable favorites.
newtype Favorites a = Favorites { toList :: [a] }
  deriving (Foldable, Show, Null, Singleton a)

-- | Equality checking is a bit expensive, since we need to sort!
--   Maybe use a 'Set' of favorites in the first place?
instance Ord a => Eq (Favorites a) where
  as == bs = Set.fromList (toList as) == Set.fromList (toList bs)

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
compareWithFavorites a favs = loop $ toList favs where
  loop []          = Dominates [] []
  loop as@(b : bs) = case comparable a b of
    POLT -> dominates b $ loop bs  -- @a@ is a new favorite, bye-bye, @b@
    POLE -> dominates b $ loop bs  -- ditto
    POEQ -> IsDominated b          -- @b@ is as least as good as @a@, bye-bye, @a@
    POGE -> IsDominated b          -- ditto
    POGT -> IsDominated b          -- ditto
    POAny -> doesnotd b $ loop bs -- don't know, compare with my other favorites
  -- add an outperformed favorite
  dominates b (Dominates bs as) = Dominates (b : bs) as
  dominates b r@IsDominated{}   = r
  -- add an uncomparable favorite
  doesnotd  b (Dominates as bs) = Dominates as (b : bs)
  doesnotd  b r@IsDominated{}   = r

-- | Compare a new set of favorites to an old one and discard
--   the new favorites that are dominated by the old ones
--   and vice verse.
--   (Skewed conservatively: faithful to the old favorites.)
--
--   @compareFavorites new old = (new', old')@
compareFavorites :: PartialOrd a => Favorites a -> Favorites a ->
                    (Favorites a, Favorites a)
compareFavorites new old = mapFst Favorites $ loop (toList new) old where
  loop []        old = ([], old)
  loop (a : new) old = case compareWithFavorites a old of
    -- Better: Discard all @old@ ones that @a@ dominates and keep @a@
    Dominates _ old -> mapFst (a:) $ loop new (Favorites old)
    -- Not better:  Discard @a@
    IsDominated{}   -> loop new old

unionCompared :: (Favorites a, Favorites a) -> Favorites a
unionCompared (Favorites new, Favorites old) = Favorites $ new ++ old

-- | After comparing, do the actual insertion.
insertCompared :: a -> Favorites a -> CompareResult a -> Favorites a
insertCompared a _ (Dominates _ as) = Favorites (a : as)
insertCompared _ l IsDominated{}    = l

-- | Compare, then insert accordingly.
--   @insert a l = insertCompared a l (compareWithFavorites a l)@
insert :: PartialOrd a => a -> Favorites a -> Favorites a
insert a l = insertCompared a l (compareWithFavorites a l)

-- | Insert all the favorites from the first list into the second.
union :: PartialOrd a => Favorites a -> Favorites a -> Favorites a
union (Favorites as) bs = List.foldr insert bs as

-- | Construct favorites from elements of a partial order.
--   The result depends on the order of the list if it
--   contains equal elements, since earlier seen elements
--   are favored over later seen equals.
--   The first element of the list is seen first.
fromList :: PartialOrd a => [a] -> Favorites a
fromList = List.foldl' (flip insert) empty

-- | 'Favorites' forms a 'Monoid' under 'empty' and 'union.
instance PartialOrd a => Semigroup (Favorites a) where
  (<>) = union
instance PartialOrd a => Monoid (Favorites a) where
  mempty  = empty
  mappend = (<>)
