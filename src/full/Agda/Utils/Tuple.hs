{-# LANGUAGE TupleSections #-}

module Agda.Utils.Tuple where

import Control.Applicative

infix 2 -*-
infix 3 /\ -- backslashes at EOL interacts badly with CPP...

(-*-) :: (a -> c) -> (b -> d) -> (a,b) -> (c,d)
(f -*- g) (x,y) = (f x, g y)

(/\) :: (a -> b) -> (a -> c) -> a -> (b,c)
(f /\ g) x = (f x, g x)

uncurry3 :: (a -> b -> c -> d) -> (a,b,c) -> d
uncurry3 f (x,y,z) = f x y z

mapPairM :: (Applicative m) => (a -> m c) -> (b -> m d) -> (a,b) -> m (c,d)
mapPairM f g (a,b) = (,) <$> f a <*> g b

mapFstM :: (Applicative m) => (a -> m c) -> (a,b) -> m (c,b)
mapFstM f (a,b) = (,b) <$> f a

mapSndM :: (Applicative m) => (b -> m d) -> (a,b) -> m (a,d)
mapSndM f (a,b) = (a,) <$> f b
