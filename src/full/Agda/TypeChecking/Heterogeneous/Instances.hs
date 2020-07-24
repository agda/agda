{-# LANGUAGE CPP                        #-}

module Agda.TypeChecking.Heterogeneous.Instances where

import Data.Semigroup ((<>))

import Agda.TypeChecking.Heterogeneous

import Agda.TypeChecking.Free.Lazy (Free(..), underBinder)
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Syntax.Internal as I
import Agda.Syntax.Internal.Generic (TermLike(..))

import Agda.Utils.Size (Sized(..))

import Agda.Utils.Impossible

---------------------------------------------------------------------
-- Agda.TypeChecking.Free.Lazy
---------------------------------------------------------------------

instance Free ContextHet where
  freeVars' = go
    where
      go Empty          = mempty
      go ((_,v) :<| vs) = freeVars' v <> underBinder (freeVars' vs)

instance Free TwinT where

---------------------------------------------------------------------
-- Instances for Agda.TypeChecking.MetaVars.Mention
---------------------------------------------------------------------

instance MentionsMeta a => MentionsMeta (Het s a) where
  mentionsMetas xs = mentionsMetas xs . unHet

instance MentionsMeta TwinT where
  mentionsMetas xs (SingleT a) = mentionsMetas xs a
  mentionsMetas xs (TwinT{twinLHS,twinRHS,twinCompat}) =
    mentionsMetas xs (twinLHS, twinRHS, twinCompat)

------------------------------------------------------------------
-- Instances for Agda.TypeChecking.Reduce
------------------------------------------------------------------
instance Instantiate TwinT where
  instantiate' = traverse instantiate'

instance Reduce TwinT where
  reduce' = traverse reduce'

instance Simplify TwinT where
  simplify' = traverse simplify'

instance Normalise TwinT where
  normalise' = traverse normalise'

instance InstantiateFull TwinT where

------------------------------------------------------------------
-- Instances for Agda.TypeChecking.Substitute
------------------------------------------------------------------
instance Subst Term TwinT where

---------------------------------------------------------------------
-- Agda.Syntax.Internal.Generic
---------------------------------------------------------------------

instance TermLike ContextHet where
  foldTerm f = foldMap (foldTerm f . snd) . unContextHet
  traverseTermM = __IMPOSSIBLE__

instance TermLike TwinT where
  traverseTermM f = \case
    SingleT a -> SingleT <$> traverseTermM f a
    TwinT{twinPid,twinLHS=a,twinRHS=b,twinCompat=c} ->
      (\a' b' c' -> TwinT{twinPid,necessary=False,twinLHS=a',twinRHS=b',twinCompat=c'}) <$>
        traverseTermM f a <*> traverseTermM f b <*> traverseTermM f c

---------------------------------------------------------------------
-- Agda.Utils.Size
---------------------------------------------------------------------

instance Sized ContextHet where
  size = length . unContextHet

