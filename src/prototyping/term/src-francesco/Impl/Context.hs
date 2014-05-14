{-# LANGUAGE GADTs #-}
module Impl.Context
    ( Context(..)
    , contextLookup
    , contextApp
    , contextPi
    , contextElemIndex
    ) where

import           Bound
import           Data.Void                        (Void)
import           Control.Arrow                    ((***))

import           Syntax.Abstract                  (Name)
import           Impl.Term
import           Term

-- Context
------------------------------------------------------------------------

-- | A 'Context' is the same as a 'Telescope', but inside out: the last
-- binding we encounter ranges over all the precedent ones.
data Context t v where
    EmptyContext :: Context t Void
    (:<)         :: Context t v -> (Name, t v) -> Context t (TermVar v)

contextLookup :: Name -> Context Type v -> Maybe (v, Type v)
contextLookup n ctx0 = go ctx0
  where
    -- Helper function so that we have the proof of equality when
    -- pattern matching the variable.
    go :: Context Type v -> Maybe (v, Type v)
    go EmptyContext         = Nothing
    go (ctx :< (n', type_)) = if n == n'
                              then Just (boundTermVar n, fmap F type_)
                              else fmap (F *** fmap F) (go ctx)

-- | Applies a 'Term' to all the variables in the context.
contextApp :: Term v -> Context Type v -> Term v
contextApp t ctx0 = eliminate t $ map (Apply . return) $ reverse $ go ctx0
  where
    go :: Context Type v -> [v]
    go EmptyContext           = []
    go (ctx :< (name, _type)) = boundTermVar name : map F (go ctx)

-- | Creates a 'Pi' type containing all the types in the 'Context' and
-- terminating with the provided 'Type'.
contextPi :: Context Type v -> Type v -> ClosedType
contextPi EmptyContext         t = t
contextPi (ctx :< (_n, type_)) t = contextPi ctx (Pi type_ (toScope t))

-- | Gets the index of a variable *from the left*.  0-indexed.  So the
-- rightmost thing will have index @length 'Context' - 1@, and the leftmost
-- thing will have index @0@.  Also returns the name at that index.
contextElemIndex :: v -> Context t v -> Named Int
contextElemIndex = undefined