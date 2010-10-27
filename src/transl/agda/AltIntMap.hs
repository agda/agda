{-# OPTIONS -cpp #-}
{-| Emulate AgdaIntMap interface on top of library FiniteMap

Implementation by Marcin Benke

-}


module AltIntMap (module AltIntMap, IntMap) where
import qualified Data.IntMap as Map
import Data.IntMap ( IntMap )

empty :: IntMap a
empty = Map.empty

add :: (Int, a) -> IntMap a -> IntMap a
add (i, x) im = Map.insert i x im

toList :: IntMap a  -> [(Int,a)]
toList = Map.toList

fromList :: [(Int,a)] -> IntMap a
fromList = Map.fromList

ilookup :: Int -> IntMap a -> Maybe a
ilookup i m = Map.lookup i m
