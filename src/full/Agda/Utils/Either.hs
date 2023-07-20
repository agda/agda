------------------------------------------------------------------------
-- | Utilities for the 'Either' type.
------------------------------------------------------------------------

module Agda.Utils.Either
  ( whileLeft
  , caseEitherM
  , mapLeft
  , mapRight
  , traverseEither
  , isLeft
  , isRight
  , fromLeft
  , fromRight
  , fromLeftM
  , fromRightM
  , maybeLeft
  , maybeRight
  , allLeft
  , allRight
  , groupByEither
  , maybeToEither
  , swapEither
  ) where

import Data.Bifunctor
import Data.Either (isLeft, isRight)
import Data.List   (unfoldr)

import Agda.Utils.List ( spanJust )
import Agda.Utils.List1 ( List1, pattern (:|), (<|) )
import qualified Agda.Utils.List1 as List1

-- | Loop while we have an exception.

whileLeft :: Monad m => (a -> Either b c) -> (a -> b -> m a) -> (a -> c -> m d) -> a -> m d
whileLeft test left right = loop where
  loop a =
    case test a of
      Left  b -> loop =<< left a b
      Right c -> right a c

-- | Monadic version of 'either' with a different argument ordering.

caseEitherM :: Monad m => m (Either a b) -> (a -> m c) -> (b -> m c) -> m c
caseEitherM mm f g = either f g =<< mm

-- | 'Either _ b' is a functor.

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft = first

-- | 'Either a' is a functor.

mapRight :: (b -> d) -> Either a b -> Either a d
mapRight = second

-- | 'Either' is bitraversable.
-- Note: From @base >= 4.10.0.0@ already present in `Data.Bitraversable`.
traverseEither :: Functor f => (a -> f c) -> (b -> f d) -> Either a b -> f (Either c d)
traverseEither f g = either (fmap Left . f) (fmap Right . g)

-- | Analogue of 'Data.Maybe.fromMaybe'.
fromLeft :: (b -> a) -> Either a b -> a
fromLeft = (id `either`)

-- | Analogue of 'Data.Maybe.fromMaybe'.
fromRight :: (a -> b) -> Either a b -> b
fromRight = (`either` id)

-- | Analogue of 'Agda.Utils.Maybe.fromMaybeM'.
fromLeftM :: Monad m => (b -> m a) -> m (Either a b) -> m a
fromLeftM f m = either return f =<< m

-- | Analogue of 'Agda.Utils.Maybe.fromMaybeM'.
fromRightM :: Monad m => (a -> m b) -> m (Either a b) -> m b
fromRightM f m = either f return =<< m

-- | Safe projection from 'Left'.
--
--   > maybeLeft (Left a) = Just a
--   > maybeLeft Right{}  = Nothing
--
maybeLeft :: Either a b -> Maybe a
maybeLeft = either Just (const Nothing)

-- | Safe projection from 'Right'.
--
--   > maybeRight (Right b) = Just b
--   > maybeRight Left{}    = Nothing
--
maybeRight :: Either a b -> Maybe b
maybeRight = either (const Nothing) Just

-- | Returns @'Just' input_with_tags_stripped@ if all elements are
-- to the 'Left', and otherwise 'Nothing'.
allLeft :: [Either a b] -> Maybe [a]
allLeft = mapM maybeLeft

-- | Returns @'Just' input_with_tags_stripped@ if all elements are
-- to the right, and otherwise 'Nothing'.
--
-- @
--  allRight xs ==
--    if all isRight xs then
--      Just (map (\(Right x) -> x) xs)
--     else
--      Nothing
-- @

allRight :: [Either a b] -> Maybe [b]
allRight = mapM maybeRight

-- | Groups a list into alternating chunks of 'Left' and 'Right' values
groupByEither :: forall a b. [Either a b] -> [Either (List1 a) (List1 b)]
groupByEither = unfoldr c
  where
  c :: [Either a b] -> Maybe (Either (List1 a) (List1 b), [Either a b])
  c []             = Nothing
  c (Left  a : xs) = Just $ first (Left  . (a :|)) $ spanJust maybeLeft  xs
  c (Right b : xs) = Just $ first (Right . (b :|)) $ spanJust maybeRight xs

-- | Convert 'Maybe' to @'Either' e@, given an error @e@ for the 'Nothing' case.
maybeToEither :: e -> Maybe a -> Either e a
maybeToEither e = maybe (Left e) Right

-- | Swap tags 'Left' and 'Right'.
swapEither :: Either a b -> Either b a
swapEither = either Right Left
