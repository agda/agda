
module Agda.Utils.Map where

import Prelude hiding (map, lookup, mapM)
import Data.Map as Map


-- UNUSED Liang-Ting Chen (05-07-2019)
-- -- * Monadic map operations
-- ---------------------------------------------------------------------------
--
-- data EitherOrBoth a b = L a | B a b | R b
--
-- -- | Not very efficient (goes via a list), but it'll do.
-- unionWithM :: (Ord k, Monad m) => (a -> a -> m a) -> Map k a -> Map k a -> m (Map k a)
-- unionWithM f m1 m2 = fromList <$> mapM combine (toList m)
--     where
--         m = unionWith both (map L m1) (map R m2)
--
--         both (L a) (R b) = B a b
--         both _     _     = __IMPOSSIBLE__
--
--         combine (k, B a b) = (,) k <$> f a b
--         combine (k, L a)   = return (k, a)
--         combine (k, R b)   = return (k, b)
--
-- UNUSED Liang-Ting Chen (05-07-2019)
-- insertWithKeyM :: (Ord k, Monad m) => (k -> a -> a -> m a) -> k -> a -> Map k a -> m (Map k a)
-- insertWithKeyM clash k x m =
--     case lookup k m of
--         Just y  -> do
--             z <- clash k x y
--             return $ insert k z m
--         Nothing -> return $ insert k x m
--
-- -- * Non-monadic map operations
-- ---------------------------------------------------------------------------
--
-- UNUSED Liang-Ting Chen (05-07-2019)
-- -- | Big conjunction over a map.
-- allWithKey :: (k -> a -> Bool) -> Map k a -> Bool
-- allWithKey f = Map.foldrWithKey (\ k a b -> f k a && b) True

-- | Filter a map based on the keys.
filterKeys :: (k -> Bool) -> Map k a -> Map k a
filterKeys p = filterWithKey (const . p)

-- UNUSED Liang-Ting Chen (05-07-2019)
-- -- | Unzip a map.
-- unzip :: Map k (a, b) -> (Map k a, Map k b)
-- unzip m = (Map.map fst m, Map.map snd m)
--
-- UNUSED Liang-Ting Chen (05-07-2019)
-- unzip3 :: Map k (a, b, c) -> (Map k a, Map k b, Map k c)
-- unzip3 m = (Map.map fst3 m, Map.map snd3 m, Map.map thd3 m)
--
