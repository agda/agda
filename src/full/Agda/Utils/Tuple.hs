{-# LANGUAGE TupleSections, GeneralizedNewtypeDeriving, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Agda.Utils.Tuple where

import Control.Applicative

import Data.Foldable
import Data.Traversable

infix 2 -*-
infix 3 /\ -- backslashes at EOL interacts badly with CPP...

-- | Bifunctoriality for pairs.
(-*-) :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
(f -*- g) ~(x,y) = (f x, g y)

-- | @mapFst f = f -*- id@
mapFst :: (a -> c) -> (a,b) -> (c,b)
mapFst f ~(x,y) = (f x, y)

-- | @mapSnd g = id -*- g@
mapSnd :: (b -> d) -> (a,b) -> (a,d)
mapSnd g ~(x,y) = (x, g y)

-- | Lifted pairing.
(/\) :: (a -> b) -> (a -> c) -> a -> (b,c)
(f /\ g) x = (f x, g x)

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

uncurry4 :: (a -> b -> c -> d -> e) -> (a,b,c,d) -> e
uncurry4 f ~(w,x,y,z) = f w x y z

-- | Monadic version of '-*-'.
mapPairM :: (Applicative m) => (a -> m c) -> (b -> m d) -> (a,b) -> m (c,d)
mapPairM f g ~(a,b) = (,) <$> f a <*> g b

-- | Monadic 'mapFst'.
mapFstM :: (Applicative m) => (a -> m c) -> (a,b) -> m (c,b)
mapFstM f ~(a,b) = (,b) <$> f a

-- | Monadic 'mapSnd'.
mapSndM :: (Applicative m) => (b -> m d) -> (a,b) -> m (a,d)
mapSndM f ~(a,b) = (a,) <$> f b

newtype List2 a = List2 { list2 :: (a,a) }
  deriving (Eq, Functor, Foldable, Traversable)
