{-# LANGUAGE CPP #-}
-- | Partially ordered monoids.

module Agda.Utils.POMonoid where

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Agda.Utils.PartialOrd

-- | Partially ordered semigroup.
--
-- Law: composition must be monotone.
--
-- @
--   related x POLE x' && related y POLE y' ==>
--   related (x <> y) POLE (x' <> y')
-- @

class (PartialOrd a, Semigroup a) => POSemigroup a where

-- | Partially ordered monoid.
--
-- Law: composition must be monotone.
--
-- @
--   related x POLE x' && related y POLE y' ==>
--   related (x <> y) POLE (x' <> y')
-- @

class (PartialOrd a, Monoid a) => POMonoid a where

-- | Completing POMonoids with inverses to form a Galois connection.
--
-- Law: composition and inverse composition form a Galois connection.
--
-- @
--   related (inverseCompose p x) POLE y <==> related x POLE (p <> y)
-- @

class POMonoid a => LeftClosedPOMonoid a where
  inverseCompose :: a -> a -> a
