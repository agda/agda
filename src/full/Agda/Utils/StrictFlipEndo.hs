
{-# LANGUAGE Strict #-}

{-|
Strict endomorphism monoid with flipped function composition order
-}

module Agda.Utils.StrictFlipEndo where

import Agda.Utils.ExpandCase
import GHC.Exts (oneShot)

newtype Endo a = Endo {appEndo :: a -> a}

instance Semigroup (Endo a) where
  {-# INLINE (<>) #-}
  Endo f <> Endo g = Endo (oneShot (\a -> case f a of a -> g a))

instance Monoid (Endo a) where
  {-# INLINE mempty #-}
  mempty = Endo \a -> a

instance ExpandCase (Endo a) where
  type Result (Endo a) = a
  {-# INLINE expand #-}
  expand k = Endo (oneShot \a -> k (oneShot \act -> appEndo act a))
