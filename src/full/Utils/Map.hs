{-# OPTIONS -cpp #-}

{-| Wrapper for the library modules @Data.FiniteMap@ (before ghc 6.4) and
    @Data.Map@ (after ghc 6.4).
-}
module Utils.Map where

#if __GLASGOW_HASKELL__ < 604
import Data.FiniteMap
#else
import qualified Data.Map as Map
#endif


#if __GLASGOW_HASKELL__ < 604

type Map a b = FiniteMap a b

emptyMap :: Ord a => Map a b
emptyMap = emptyFM

unitMap :: Ord a => a -> b -> Map a b
unitMap = unitFM

buildMap :: Ord a => [(a,b)] -> Map a b
buildMap = listToFM

lookupMap :: Ord a => a -> Map a b -> Maybe b
lookupMap x m = lookupFM m x

lookupMap' :: Ord a => b -> a -> Map a b -> b
lookupMap' e x m = lookupWithDefaultFM m e x

updateMap :: Ord a => a -> b -> Map a b -> Map a b
updateMap x v m = addToFM m x v

isInMap :: Ord a => a -> Map a b -> Bool
isInMap x m = elemFM x m

plusMap :: Ord a => Map a b -> Map a b -> Map a b
plusMap = plusFM

plusMapC :: Ord a => (b -> b -> b) -> Map a b -> Map a b -> Map a b
plusMapC = plusFM_C

intersectMap :: Ord a => Map a b -> Map a b -> Map a b
intersectMap = intersectFM

keysMap :: Ord a => Map a b -> [a]
keysMap = keysFM

elemsMap :: Ord a => Map a b -> [b]
elemsMap = eltsFM

assocsMap :: Ord a => Map a b -> [(a,b)]
assocsMap = fmToList

isEmptyMap :: Ord a => Map a b -> Bool
isEmptyMap = isEmptyFM

#else

type Map a b = Map.Map a b

emptyMap :: Ord a => Map a b
emptyMap = Map.empty

unitMap :: Ord a => a -> b -> Map a b
unitMap = Map.singleton

buildMap :: Ord a => [(a,b)] -> Map a b
buildMap = Map.fromList

lookupMap :: Ord a => a -> Map a b -> Maybe b
lookupMap x m = Map.lookup x m

lookupMap' :: Ord a => b -> a -> Map a b -> b
lookupMap' e x m = Map.findWithDefault e x m

updateMap :: Ord a => a -> b -> Map a b -> Map a b
updateMap x v m = Map.insert x v m

isInMap :: Ord a => a -> Map a b -> Bool
isInMap x m = Map.member x m

plusMap :: Ord a => Map a b -> Map a b -> Map a b
plusMap = Map.union

plusMapC :: Ord a => (b -> b -> b) -> Map a b -> Map a b -> Map a b
plusMapC = Map.unionWith

intersectMap :: Ord a => Map a b -> Map a b -> Map a b
intersectMap = Map.intersection

keysMap :: Ord a => Map a b -> [a]
keysMap = Map.keys

elemsMap :: Ord a => Map a b -> [b]
elemsMap = Map.elems

assocsMap :: Ord a => Map a b -> [(a,b)]
assocsMap = Map.assocs

isEmptyMap :: Ord a => Map a b -> Bool
isEmptyMap = Map.null

#endif
