module Impl.Context
    ( -- * 'Ctx'
      Ctx(..)
    , ClosedCtx
    , empty
    , singleton
    , extend
    , lookup
    , app
    , pi
    , length
    , elemIndex
    , (++)
    , weaken
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Bound                            hiding (instantiate)
import           Data.Void                        (Void, absurd)
import           Control.Arrow                    ((***))

import           Syntax.Abstract                  (Name)
import           Impl.Term
import           Term

-- Ctx
------------------------------------------------------------------------

-- | A 'Ctx' is the same as a 'Tel', but inside out: the last
-- binding we encounter ranges over all the precedent ones.
data Ctx v0 t v where
    Empty :: Ctx v0 t v0
    (:<)  :: Ctx v0 t v -> (Name, t v) -> Ctx v0 t (TermVar v)

type ClosedCtx = Ctx Void

empty :: Ctx v0 t v0
empty = Empty

singleton :: Name -> t v0 -> Ctx v0 t (TermVar v0)
singleton name t = Empty :< (name, t)

extend :: Ctx v0 t v -> Name -> t v -> Ctx v0 t (TermVar v)
extend ctx n type_ = ctx :< (n, type_)

lookup :: Name -> Ctx v0 Type v -> Maybe (v, Type v)
lookup n ctx0 = go ctx0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: Ctx v0 Type v -> Maybe (v, Type v)
    go Empty                = Nothing
    go (ctx :< (n', type_)) = if n == n'
                              then Just (boundTermVar n, fmap F type_)
                              else fmap (F *** fmap F) (go ctx)

-- | Applies a 'Term' to all the variables in the context.  The
-- variables are applied from left to right.
app :: Term v -> Ctx v0 Type v -> Term v
app t ctx0 = eliminate t $ map (Apply . return) $ reverse $ go ctx0
  where
    go :: Ctx v0 Type v -> [v]
    go Empty                  = []
    go (ctx :< (name, _type)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Ctx' and
-- terminating with the provided 'Type'.
pi :: Ctx v0 Type v -> Type v -> Type v0
pi Empty                t = t
pi (ctx :< (_n, type_)) t = pi ctx (Pi type_ (toScope t))

length :: Ctx v0 t v -> Int
length Empty      = 0
length (ctx :< _) = 1 + length ctx

-- | Gets the index of a variable *from the left*.  0-indexed.  So the
-- rightmost thing will have index @length 'Ctx' - 1@, and the leftmost
-- thing will have index @0@.  Also returns the name at that index.
elemIndex :: v -> ClosedCtx t v -> Named Int
elemIndex v0 ctx0 = fmap (length ctx0 -) $ go ctx0 v0
  where
    go :: ClosedCtx t v -> v -> Named Int
    go Empty v = absurd v
    go (_ctx :< (n, _type)) (B _) = named n 1
    go ( ctx :< _         ) (F v) = fmap (+ 1) $ go ctx v

(++) :: Ctx v0 t v1 -> Ctx v1 t v2 -> Ctx v0 t v2
ctx1 ++ Empty               = ctx1
ctx1 ++ (ctx2 :< namedType) = (ctx1 ++ ctx2) :< namedType

weaken :: Ctx v0 t v -> v0 -> v
weaken Empty      v = v
weaken (ctx :< _) v = F (weaken ctx v)
