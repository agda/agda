{-# OPTIONS -cpp #-}
{-| Emulate AgdaIntMap interface on top of library FiniteMap

Implementation by Marcin Benke

-}


module AltIntMap where
import Data.FiniteMap

type IntMap a  = FiniteMap Int a


empty :: IntMap a
empty = emptyFM

add :: (Int, a) -> IntMap a -> IntMap a
add (i, x) im = addToFM im i x

toList :: IntMap a  -> [(Int,a)]
toList = fmToList

fromList :: [(Int,a)] -> IntMap a  
fromList = listToFM

ilookup :: Int -> IntMap a -> Maybe a
ilookup i m = lookupFM m i

#if __GLASGOW_HASKELL__ < 604
-- With ghc 6.4 an instance is already available
instance (Show a,Show b) => Show (FiniteMap a b) where
    showsPrec _ s = showString "{" . f (fmToList s) . showString "}"
        where f []     = id
              f [x]    = g x 
              f (x:xs) = g x . showString ", " . f xs
              g (i, r) = shows i . showString "->" . shows r
#endif

