module Agda.Utils.Applicative
       ( (?*>)
       , (?$>)
       )
       where

import Control.Applicative

-- | Guard: return the action @f@ only if the boolean is @True@
(?*>) :: Alternative f => Bool -> f a -> f a
b ?*> f = if b then f else empty

-- | Guard: return the value @a@ only if the boolean is @True@
(?$>) :: Alternative f => Bool -> a -> f a
b ?$> a = b ?*> pure a
