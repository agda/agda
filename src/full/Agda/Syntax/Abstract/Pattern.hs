{-# LANGUAGE CPP                       #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | Auxiliary functions to handle patterns in the abstract syntax.
--
--   Generic and specific traversals.

module Agda.Syntax.Abstract.Pattern where

import Control.Monad ((>=>))
import Control.Applicative (Applicative)

import Data.Foldable (Foldable, foldMap)
import Data.Traversable (Traversable, traverse)
import Data.Functor
import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Concrete (FieldAssignment', exprFieldA)
import Agda.Syntax.Abstract as A

#include "undefined.h"
import Agda.Utils.Impossible

-- * Generic traversals

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

instance MapNamedArgPattern a => MapNamedArgPattern [a]                  where
instance MapNamedArgPattern a => MapNamedArgPattern (FieldAssignment' a) where
instance MapNamedArgPattern a => MapNamedArgPattern (Maybe a)            where

-- | Generic pattern traversal.

class APatternLike a p | p -> a where

  -- | Fold pattern.
  foldrAPattern
    :: Monoid m
    => (Pattern' a -> m -> m)
         -- ^ Combine a pattern and the value computed from its subpatterns.
    -> p -> m

  default foldrAPattern
    :: (Monoid m, Foldable f, APatternLike a b, f b ~ p)
    => (Pattern' a -> m -> m) -> p -> m
  foldrAPattern = foldMap . foldrAPattern

  -- | Traverse pattern.
  traverseAPatternM :: (Monad m
#if __GLASGOW_HASKELL__ <= 708
    , Applicative m, Functor m
#endif
    ) => (Pattern' a -> m (Pattern' a))  -- ^ @pre@: Modification before recursion.
      -> (Pattern' a -> m (Pattern' a))  -- ^ @post@: Modification after recursion.
      -> p -> m p

  default traverseAPatternM :: (Traversable f, APatternLike a q, f q ~ p, Monad m
#if __GLASGOW_HASKELL__ <= 708
    , Applicative m, Functor m
#endif
    ) => (Pattern' a -> m (Pattern' a))
      -> (Pattern' a -> m (Pattern' a))
      -> p -> m p
  traverseAPatternM pre post = traverse $ traverseAPatternM pre post

-- | Compute from each subpattern a value and collect them all in a monoid.

foldAPattern :: (APatternLike a p, Monoid m) => (Pattern' a -> m) -> p -> m
foldAPattern f = foldrAPattern $ \ p m -> f p `mappend` m

-- | Traverse pattern(s) with a modification before the recursive descent.

preTraverseAPatternM :: (APatternLike a b, Monad m
#if __GLASGOW_HASKELL__ <= 708
  , Applicative m, Functor m
#endif
  ) => (Pattern' a -> m (Pattern' a))  -- ^ @pre@: Modification before recursion.
    -> b -> m b
preTraverseAPatternM pre p = traverseAPatternM pre return p

-- | Traverse pattern(s) with a modification after the recursive descent.

postTraverseAPatternM :: (APatternLike a b, Monad m
#if __GLASGOW_HASKELL__ <= 708
  , Applicative m, Functor m
#endif
  ) => (Pattern' a -> m (Pattern' a))  -- ^ @post@: Modification after recursion.
    -> b -> m b
postTraverseAPatternM post p = traverseAPatternM return post p

-- Interesting instance:

instance APatternLike a (Pattern' a) where
  foldrAPattern f p = f p $
    case p of
      AsP _ _ p          -> foldrAPattern f p
      ConP _ _ ps        -> foldrAPattern f ps
      DefP _ _ ps        -> foldrAPattern f ps
      RecP _ ps          -> foldrAPattern f ps
      PatternSynP _ _ ps -> foldrAPattern f ps
      VarP _             -> mempty
      ProjP _ _ _        -> mempty
      WildP _            -> mempty
      DotP _ _ _         -> mempty
      AbsurdP _          -> mempty
      LitP _             -> mempty

  traverseAPatternM pre post = pre >=> recurse >=> post
    where
    recurse p = case p of
      -- Non-recursive cases:
      A.VarP{}             -> return p
      A.WildP{}            -> return p
      A.DotP{}             -> return p
      A.LitP{}             -> return p
      A.AbsurdP{}          -> return p
      A.ProjP{}            -> return p
      -- Recursive cases:
      A.ConP        i ds ps -> A.ConP        i ds <$> traverseAPatternM pre post ps
      A.DefP        i q  ps -> A.DefP        i q  <$> traverseAPatternM pre post ps
      A.AsP         i x  p  -> A.AsP         i x  <$> traverseAPatternM pre post p
      A.RecP        i    ps -> A.RecP        i    <$> traverseAPatternM pre post ps
      A.PatternSynP i x  ps -> A.PatternSynP i x  <$> traverseAPatternM pre post ps

-- The following instances need UndecidableInstances
-- for the FunctionalDependency (since injectivity is not taken into account).

instance APatternLike a b => APatternLike a (Arg b)              where
instance APatternLike a b => APatternLike a (Named n b)          where
instance APatternLike a b => APatternLike a [b]                  where
instance APatternLike a b => APatternLike a (Maybe b)            where
instance APatternLike a b => APatternLike a (FieldAssignment' b) where

-- * Specific folds

-- | Collect pattern variables in left-to-right textual order.

patternVars :: forall a p. APatternLike a p => p -> [A.Name]
patternVars p = foldAPattern f p `appEndo` []
  where
  -- We use difference lists @[A.Name] -> [A.Name]@ to avoid reconcatenation.
  f :: Pattern' a -> Endo [A.Name]
  f = \case
    A.VarP x         -> Endo (x :)
    A.AsP _ x _      -> Endo (x :)
    A.LitP        {} -> mempty
    A.ConP        {} -> mempty
    A.RecP        {} -> mempty
    A.DefP        {} -> mempty
    A.ProjP       {} -> mempty
    A.WildP       {} -> mempty
    A.DotP        {} -> mempty
    A.AbsurdP     {} -> mempty
    A.PatternSynP {} -> mempty

-- | Check if a pattern contains a specific (sub)pattern.

containsAPattern :: APatternLike a p => (Pattern' a -> Bool) -> p -> Bool
containsAPattern f = getAny . foldAPattern (Any . f)

-- | Check if a pattern contains an absurd pattern.
--   For instance, @suc ()@, does so.
--
--   Precondition: contains no pattern synonyms.

containsAbsurdPattern :: APatternLike a p => p -> Bool
containsAbsurdPattern = containsAPattern $ \case
    A.PatternSynP{} -> __IMPOSSIBLE__
    A.AbsurdP{}     -> True
    _               -> False

-- | Check if a pattern contains an @-pattern.
--
--   Precondition: contains no pattern synonyms.

containsAsPattern :: APatternLike a p => p -> Bool
containsAsPattern = containsAPattern $ \case
    A.PatternSynP{} -> __IMPOSSIBLE__
    A.AsP{}         -> True
    _               -> False
