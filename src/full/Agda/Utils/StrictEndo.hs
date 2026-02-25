{-# LANGUAGE Strict #-}

module Agda.Utils.StrictEndo where

import Agda.Utils.ExpandCase
import GHC.Exts (oneShot)

newtype Endo a = Endo {appEndo :: a -> a}

instance Semigroup (Endo a) where
  {-# INLINE (<>) #-}
  Endo f <> Endo g = Endo (oneShot (\a -> case g a of b -> f b))

instance Monoid (Endo a) where
  {-# INLINE mempty #-}
  mempty = Endo \a -> a

instance ExpandCase (Endo a) where
  type Result (Endo a) = a
  {-# INLINE expand #-}
  expand k = Endo (oneShot \a -> k (oneShot \act -> appEndo act a))
