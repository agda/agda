{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Utils.Tuple
  ( (-*-)
  , mapFst
  , mapSnd
  , (/\)
  , sortPair
  , fst3
  , snd3
  , thd3
  , swap
  , uncurry3
  , uncurry4
  , mapPairM
  , mapFstM
  , mapSndM
  , Pair(..)
  ) where

import Control.Arrow   ( (&&&) )
import Control.DeepSeq ( NFData )

import Data.Bifunctor  ( bimap, first, second )
import Data.Tuple      ( swap )

import GHC.Generics    ( Generic )

infix 2 -*-
infix 3 /\ -- backslashes at EOL interact badly with CPP...

-- | Bifunctoriality for pairs.
(-*-) :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
(-*-) = bimap

-- | @mapFst f = f -*- id@
mapFst :: (a -> c) -> (a,b) -> (c,b)
mapFst = first

-- | @mapSnd g = id -*- g@
mapSnd :: (b -> d) -> (a,b) -> (a,d)
mapSnd = second

-- | Lifted pairing.
(/\) :: (a -> b) -> (a -> c) -> a -> (b,c)
(/\) = (&&&)

-- | Order a pair.
sortPair :: Ord a => (a, a) -> (a, a)
sortPair p@(x, y)
  | x <= y    = p
  | otherwise = (y, x)

-- * Triple (stolen from Data.Tuple.HT)

{-# INLINE fst3 #-}
fst3 :: (a,b,c) -> a
fst3 ~(x,_,_) = x

{-# INLINE snd3 #-}
snd3 :: (a,b,c) -> b
snd3 ~(_,x,_) = x

{-# INLINE thd3 #-}
thd3 :: (a,b,c) -> c
thd3 ~(_,_,x) = x

{-# INLINE uncurry3 #-}
uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f ~(x,y,z) = f x y z

{-# INLINE uncurry4 #-}
uncurry4 :: (a -> b -> c -> d -> e) -> (a,b,c,d) -> e
uncurry4 f ~(w,x,y,z) = f w x y z

-- | Monadic version of '-*-'.
mapPairM :: (Applicative m) => (a -> m c) -> (b -> m d) -> (a,b) -> m (c,d)
mapPairM f g ~(a,b) = (,) <$> f a <*> g b

-- | Monadic 'mapFst'.
mapFstM :: Functor m => (a -> m c) -> (a,b) -> m (c,b)
mapFstM f ~(a,b) = (,b) <$> f a

-- | Monadic 'mapSnd'.
mapSndM :: Functor m => (b -> m d) -> (a,b) -> m (a,d)
mapSndM f ~(a,b) = (a,) <$> f b

data Pair a = Pair a a
  deriving (Show, Eq, Generic, Functor, Foldable, Traversable)

instance Applicative Pair where
  pure a                  = Pair a a
  Pair f f' <*> Pair a a' = Pair (f a) (f' a')

instance NFData a => NFData (Pair a)
