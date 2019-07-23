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

class (PartialOrd a, Semigroup a, Monoid a) => POMonoid a where

-- | Completing POMonoids with inverses to form a Galois connection.
--
-- Law: composition and inverse composition form a Galois connection.
--
-- @
--   related (inverseCompose p x) POLE y <==> related x POLE (p <> y)
-- @

class POMonoid a => LeftClosedPOMonoid a where
  inverseCompose :: a -> a -> a


-- | @hasLeftAdjoint x@ checks whether
--   @x^-1 := x `inverseCompose` mempty@ is such that
--   @x `inverseCompose` y == x^-1 <> y@ for any @y@.
hasLeftAdjoint :: LeftClosedPOMonoid a => a -> Bool
hasLeftAdjoint x = related (inverseCompose x mempty <> x) POLE mempty
  -- It is enough to check the above, because of the following proof:
  -- I will write _\_ for `inverseCompose`, id for mempty, and _._ for (<>).
  -- Assume (*) x^-1 . x <= id, as checked.
  -- Show x^-1 . y <=> x \ y
  --
  -- 1. (>=)
     -- id     <= x . (x \ id)      (galois)
     -- id . y <= x . (x \ id) . y
     -- y      <= x . (x \ id) . y
     -- x \ y  <= (x \ id) . y      (galois)
     -- x^-1 . y >= x \ y           qed
  --
  -- 2. (<=)
     --        y <=        x . (x \ y)   (galois)
     -- x^-1 . y <= x^-1 . x . (x \ y)
     --          <= id       . (x \ y)   (*)
     --          <= x \ y
     -- x^-1 . y <= x \ y                qed
