{-# LANGUAGE TupleSections #-}

module Agda.Utils.Tuple where

import Control.Applicative

infix 2 -*-
infix 3 /\ -- backslashes at EOL interacts badly with CPP...

-- | Bifunctoriality for pairs.
(-*-) :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
(f -*- g) (x,y) = (f x, g y)

-- | @mapFst f = f -*- id@
mapFst :: (a -> c) -> (a,b) -> (c,b)
mapFst f (x,y) = (f x, y)

-- | @mapSnd g = id -*- g@
mapSnd :: (b -> d) -> (a,b) -> (a,d)
mapSnd g (x,y) = (x, g y)

-- | Lifted pairing.
(/\) :: (a -> b) -> (a -> c) -> a -> (b,c)
(f /\ g) x = (f x, g x)

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (x,y,z) = f x y z

-- | Monadic version of '-*-'.
mapPairM :: (Applicative m) => (a -> m c) -> (b -> m d) -> (a,b) -> m (c,d)
mapPairM f g (a,b) = (,) <$> f a <*> g b

-- | Monadic 'mapFst'.
mapFstM :: (Applicative m) => (a -> m c) -> (a,b) -> m (c,b)
mapFstM f (a,b) = (,b) <$> f a

-- | Monadic 'mapSnd'.
mapSndM :: (Applicative m) => (b -> m d) -> (a,b) -> m (a,d)
mapSndM f (a,b) = (a,) <$> f b
