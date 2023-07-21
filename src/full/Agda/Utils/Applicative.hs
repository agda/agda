{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Utils.Applicative
       ( (?*>)
       , (?$>)
       , foldA
       , foldMapA
       , forA
       )
       where

import Control.Applicative
import Data.Monoid ( Alt(..) )
import Data.Traversable ( for )

-- | Better name for 'for'.
forA :: (Traversable t, Applicative f) => t a -> (a -> f b) -> f (t b)
forA = for

-- | Guard: return the action @f@ only if the boolean is @True@
(?*>) :: Alternative f => Bool -> f a -> f a
b ?*> f = if b then f else empty

-- | Guard: return the value @a@ only if the boolean is @True@
(?$>) :: Alternative f => Bool -> a -> f a
b ?$> a = b ?*> pure a

-- | Branch over a 'Foldable' collection of values.
foldA :: (Alternative f, Foldable t) => t a -> f a
foldA = foldMapA pure

-- | Branch over a 'Foldable' collection of values using the supplied
--   action.
foldMapA :: (Alternative f, Foldable t) => (a -> f b) -> t a -> f b
foldMapA f = getAlt . foldMap (Alt . f)
