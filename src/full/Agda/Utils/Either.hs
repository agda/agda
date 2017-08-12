------------------------------------------------------------------------
-- | Utilities for the 'Either' type
------------------------------------------------------------------------

module Agda.Utils.Either where

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

-- | 'Either' is a bifunctor.

mapEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
mapEither f g = either (Left . f) (Right . g)

-- | 'Either _ b' is a functor.

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f = mapEither f id

-- | 'Either a' is a functor.

mapRight :: (b -> d) -> Either a b -> Either a d
mapRight = mapEither id

-- | 'Either' is bitraversable.

traverseEither :: Functor f => (a -> f c) -> (b -> f d) -> Either a b -> f (Either c d)
traverseEither f g = either (fmap Left . f) (fmap Right . g)

-- | Returns 'True' iff the argument is @'Right' x@ for some @x@.
--   Note: from @base >= 4.7.0.0@ already present in @Data.Either@.
isRight :: Either a b -> Bool
isRight (Right _) = True
isRight (Left  _) = False

-- | Returns 'True' iff the argument is @'Left' x@ for some @x@.
--   Note: from @base >= 4.7.0.0@ already present in @Data.Either@.
isLeft :: Either a b -> Bool
isLeft (Right _) = False
isLeft (Left _)  = True

-- | Analogue of 'Data.Maybe.fromMaybe'.
fromLeft :: (b -> a) -> Either a b -> a
fromLeft = either id

-- | Analogue of 'Data.Maybe.fromMaybe'.
fromRight :: (a -> b) -> Either a b -> b
fromRight f = either f id

-- | Analogue of 'Agda.Utils.Maybe.fromMaybeM'.
fromLeftM :: Monad m => (b -> m a) -> Either a b -> m a
fromLeftM = either return

-- | Analogue of 'Agda.Utils.Maybe.fromMaybeM'.
fromRightM :: Monad m => (a -> m b) -> Either a b -> m b
fromRightM f = either f return

-- | Safe projection from 'Left'.
--   @
--     maybeLeft (Left a) = Just a
--     maybeLeft Right{}  = Nothing
--   @
maybeLeft :: Either a b -> Maybe a
maybeLeft = either Just (const Nothing)

-- | Safe projection from 'Right'.
--   @
--     maybeRight (Right b) = Just b
--     maybeRight Left{}    = Nothing
--   @
maybeRight :: Either a b -> Maybe b
maybeRight = either (const Nothing) Just

-- | Returns @'Just' <input with tags stripped>@ if all elements are
-- to the 'Left', and otherwise 'Nothing'.
allLeft :: [Either a b] -> Maybe [a]
allLeft = mapM maybeLeft

-- | Returns @'Just' <input with tags stripped>@ if all elements are
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

-- | Convert 'Maybe' to @'Either' ()'@
maybeToEither :: Maybe a -> Either () a
maybeToEither = maybe (Left ()) Right
