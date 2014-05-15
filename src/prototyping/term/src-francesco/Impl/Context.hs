{-# LANGUAGE GADTs #-}
module Impl.Context
    ( Context(..)
    , ClosedContext
    , lookup
    , app
    , pi
    , length
    , elemIndex
    , toTele
    , (++)
    , weaken
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Bound
import           Data.Void                        (Void, absurd)
import           Control.Arrow                    ((***))

import           Syntax.Abstract                  (Name)
import           Impl.Term
import qualified Impl.Telescope                   as Tel
import           Term

-- Context
------------------------------------------------------------------------

-- | A 'Context' is the same as a 'Telescope', but inside out: the last
-- binding we encounter ranges over all the precedent ones.
data Context v0 t v where
    Empty :: Context v0 t v0
    (:<)  :: Context v0 t v -> (Name, t v) -> Context v0 t (TermVar v)

type ClosedContext = Context Void

lookup :: Name -> Context v0 Type v -> Maybe (v, Type v)
lookup n ctx0 = go ctx0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: Context v0 Type v -> Maybe (v, Type v)
    go Empty                = Nothing
    go (ctx :< (n', type_)) = if n == n'
                              then Just (boundTermVar n, fmap F type_)
                              else fmap (F *** fmap F) (go ctx)

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
app :: Term v -> Context v0 Type v -> Term v
app t ctx0 = eliminate t $ map (Apply . return) $ reverse $ go ctx0
  where
    go :: Context v0 Type v -> [v]
    go Empty                  = []
    go (ctx :< (name, _type)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Context' and
-- terminating with the provided 'Type'.
pi :: Context v0 Type v -> Type v -> Type v0
pi Empty                t = t
pi (ctx :< (_n, type_)) t = pi ctx (Pi type_ (toScope t))

length :: Context v0 t v -> Int
length Empty      = 0
length (ctx :< _) = 1 + length ctx

-- | Gets the index of a variable *from the left*.  0-indexed.  So the
-- rightmost thing will have index @length 'Context' - 1@, and the leftmost
-- thing will have index @0@.  Also returns the name at that index.
elemIndex :: v -> ClosedContext t v -> Named Int
elemIndex v0 ctx0 = fmap (length ctx0 -) $ go ctx0 v0
  where
    go :: ClosedContext t v -> v -> Named Int
    go Empty v = absurd v
    go (_ctx :< (n, _type)) (B _) = named n 1
    go ( ctx :< _         ) (F v) = fmap (+ 1) $ go ctx v

toTele :: ClosedContext t v -> t v -> Tel.ClosedTelescope t
toTele ctx0 t = go ctx0 (Tel.Empty t)
  where
    go :: ClosedContext t v -> Tel.Telescope t v -> Tel.ClosedTelescope t
    go Empty               tel = tel
    go (ctx :< (_, type_)) tel = go ctx (type_ Tel.:> tel)

(++) :: Context v0 t v1 -> Context v1 t v2 -> Context v0 t v2
ctx1 ++ Empty               = ctx1
ctx1 ++ (ctx2 :< namedType) = (ctx1 ++ ctx2) :< namedType

weaken :: Context v0 t v -> v0 -> v
weaken Empty      v = v
weaken (ctx :< _) v = F (weaken ctx v)
