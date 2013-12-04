
module Agda.Utils.Function where

-- | Iteration to fixed-point.
--
--   @iterateUntil r f a0@ iterates endofunction @f@, starting with @a0@,
--   until @r@ relates its result to its input, i.e., @f a `r` a@.
--
--   This is the generic pattern behind saturation algorithms.
--
--   If @f@ is monotone with regard to @r@,
--   meaning @a `r` b@ implies @f a `r` f b@,
--   and @f@-chains starting with @a0@ are finite
--   then iteration is guaranteed to terminate.
--
--   A typical instance will work on sets, and @r@ could be set inclusion,
--   and @a0@ the empty set, and @f@ the step function of a saturation algorithm.
iterateUntil :: (a -> a -> Bool) -> (a -> a) -> a -> a
iterateUntil r f = loop where
  loop a = if r a' a then a' else loop a'
    where a' = f a

-- | Monadic version of 'iterateUntil'.
iterateUntilM :: Monad m => (a -> a -> Bool) -> (a -> m a) -> a -> m a
iterateUntilM r f = loop where
  loop a = do
    a' <- f a
    if r a' a then return a' else loop a'

-- | @'iterate'' n f x@ applies @f@ to @x@ @n@ times and returns the
-- result.
--
-- The applications are calculated strictly.

iterate' :: Integral i => i -> (a -> a) -> a -> a
iterate' 0 f x             = x
iterate' n f x | n > 0     = iterate' (n - 1) f $! f x
               | otherwise = error "iterate': Negative input."

rot3 :: (a -> b -> c -> d) -> b -> c -> a -> d
rot3 f b c a = f a b c
