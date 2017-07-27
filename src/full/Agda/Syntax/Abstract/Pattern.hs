{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonoLocalBinds          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE UndecidableInstances      #-}

module Agda.Syntax.Abstract.Pattern where

import Data.Foldable (Foldable, foldMap)
import Data.Functor

import Agda.Syntax.Common
import Agda.Syntax.Concrete (FieldAssignment', exprFieldA)
import Agda.Syntax.Abstract as A

type NAP = NamedArg Pattern

class MapNamedArgPattern a  where
  mapNamedArgPattern :: (NAP -> NAP) -> a -> a

  default mapNamedArgPattern
     :: (Functor f, MapNamedArgPattern a', a ~ f a') => (NAP -> NAP) -> a -> a
  mapNamedArgPattern = fmap . mapNamedArgPattern

instance MapNamedArgPattern NAP where
  mapNamedArgPattern f p =
    case namedArg p of
      -- no sub patterns:
      VarP{}    -> f p
      WildP{}   -> f p
      DotP{}    -> f p
      LitP{}    -> f p
      AbsurdP{} -> f p
      ProjP{}   -> f p
      -- list of NamedArg subpatterns:
      ConP i qs ps       -> f $ setNamedArg p $ ConP i qs $ mapNamedArgPattern f ps
      DefP i qs ps       -> f $ setNamedArg p $ DefP i qs $ mapNamedArgPattern f ps
      PatternSynP i x ps -> f $ setNamedArg p $ PatternSynP i x $ mapNamedArgPattern f ps
      -- Pattern subpattern(s):
      -- RecP: we copy the NamedArg info to the subpatterns but discard it after recursion
      RecP i fs          -> f $ setNamedArg p $ RecP i $ map (fmap namedArg) $ mapNamedArgPattern f $ map (fmap (setNamedArg p)) fs
      -- AsP: we hand the NamedArg info to the subpattern
      AsP i x p0         -> f $ updateNamedArg (AsP i x) $ mapNamedArgPattern f $ setNamedArg p p0

instance MapNamedArgPattern a => MapNamedArgPattern [a] where

instance MapNamedArgPattern a => MapNamedArgPattern (FieldAssignment' a) where

instance MapNamedArgPattern a => MapNamedArgPattern (Maybe a) where

-- | Generic pattern traversal.

class APatternLike a p | p -> a where
  foldrAPattern
    :: Monoid m
    => (Pattern' a -> m -> m)
         -- ^ Combine a pattern and the value computed from its subpatterns.
    -> p -> m

  default foldrAPattern
    :: (Monoid m, Foldable f, APatternLike a b, f b ~ p)
    => (Pattern' a -> m -> m)
    -> p -> m
  foldrAPattern = foldMap . foldrAPattern

-- | Compute from each subpattern a value and collect them all in a monoid.
foldAPattern :: (APatternLike a p, Monoid m) => (Pattern' a -> m) -> p -> m
foldAPattern f = foldrAPattern $ \ p m -> f p `mappend` m

instance APatternLike a (Pattern' a) where
  foldrAPattern f p = f p $
    case p of
      AsP _ _ p          -> fold p
      ConP _ _ ps        -> fold ps
      DefP _ _ ps        -> fold ps
      RecP _ ps          -> fold ps
      PatternSynP _ _ ps -> fold ps
      VarP _             -> mempty
      ProjP _ _ _        -> mempty
      WildP _            -> mempty
      DotP _ _ _         -> mempty
      AbsurdP _          -> mempty
      LitP _             -> mempty
    where
    fold = foldrAPattern f

-- The following instances need UndecidableInstances
-- for the FunctionalDependency (since injectivity is not taken into account).

instance APatternLike a b => APatternLike a (Arg b)              where
instance APatternLike a b => APatternLike a (Named n b)          where
instance APatternLike a b => APatternLike a [b]                  where
instance APatternLike a b => APatternLike a (Maybe b)            where
instance APatternLike a b => APatternLike a (FieldAssignment' b) where
