{-# LANGUAGE Strict #-}

module Agda.Utils.StrictEndo where

import GHC.Exts (oneShot)

newtype Endo a = Endo {appEndo :: a -> a}

instance Semigroup (Endo a) where
  {-# INLINE (<>) #-}
  Endo f <> Endo g = Endo (oneShot (\ a -> case g a of b -> f b))

instance Monoid (Endo a) where
  {-# INLINE mempty #-}
  mempty = Endo \ a -> a
