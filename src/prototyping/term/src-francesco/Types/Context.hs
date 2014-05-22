module Types.Context
    ( -- * 'Ctx'
      Ctx(..)
    , ClosedCtx
    , singleton
    , lookupName
    , getVar
    , length
    , elemIndex
    , (++)
    , weaken
    ) where

import           Prelude                          hiding (pi, length, lookup, (++))

import           Bound
import           Data.Void                        (Void, absurd)
import           Control.Arrow                    ((***))

import           Syntax.Abstract                  (Name)
import           Types.Var

-- Ctx
------------------------------------------------------------------------

-- | A 'Ctx' is the same as a 'Tel', but inside out: the last
-- binding we encounter ranges over all the precedent ones.
data Ctx v0 t v where
    Empty :: Ctx v0 t v0
    Snoc  :: Ctx v0 t v -> (Name, t v) -> Ctx v0 t (TermVar v)

type ClosedCtx = Ctx Void

singleton :: Name -> t v0 -> Ctx v0 t (TermVar v0)
singleton name t = Snoc Empty (name, t)

lookupName :: Functor t => Name -> Ctx v0 t v -> Maybe (v, t v)
lookupName n ctx0 = go ctx0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: Functor t => Ctx v0 t v -> Maybe (v, t v)
    go Empty                  = Nothing
    go (Snoc ctx (n', type_)) = if n == n'
                                then Just (boundTermVar n, fmap F type_)
                                else fmap (F *** fmap F) (go ctx)

getVar :: forall t v. Functor t => v -> ClosedCtx t v -> t v
getVar v0 ctx0 = go ctx0 v0
  where
    go :: forall v'. ClosedCtx t v' -> v' -> t v'
    go Empty                 v     = absurd v
    go (Snoc _ (_, type_)) (B _) = fmap F type_
    go (Snoc ctx _)        (F v) = fmap F (go ctx v)

length :: Ctx v0 t v -> Int
length Empty        = 0
length (Snoc ctx _) = 1 + length ctx

-- | Gets the index of a variable *from the left*.  0-indexed.  So the
-- rightmost thing will have index @length 'Ctx' - 1@, and the leftmost
-- thing will have index @0@.  Also returns the name at that index.
elemIndex :: v -> ClosedCtx t v -> Named Int
elemIndex v0 ctx0 = fmap (length ctx0 -) $ go ctx0 v0
  where
    go :: ClosedCtx t v -> v -> Named Int
    go Empty v = absurd v
    go (Snoc _ctx (n, _type)) (B _) = named n 1
    go (Snoc  ctx _         ) (F v) = fmap (+ 1) $ go ctx v

(++) :: Ctx v0 t v1 -> Ctx v1 t v2 -> Ctx v0 t v2
ctx1 ++ Empty                 = ctx1
ctx1 ++ (Snoc ctx2 namedType) = Snoc (ctx1 ++ ctx2) namedType

weaken :: Ctx v0 t v -> v0 -> v
weaken Empty        v = v
weaken (Snoc ctx _) v = F (weaken ctx v)
