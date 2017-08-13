{-# LANGUAGE CPP                    #-}
{-# LANGUAGE TypeFamilies           #-}  -- because of type equality ~
{-# LANGUAGE UndecidableInstances   #-}  -- because of func. deps.

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

module Agda.Syntax.Internal.Pattern where

import Control.Applicative
import Control.Monad.State

import Data.Maybe
import Data.Monoid
import qualified Data.List as List
import Data.Foldable (Foldable, foldMap)
import Data.Traversable (Traversable, traverse)

import Agda.Syntax.Common
import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Internal
import qualified Agda.Syntax.Internal as I

import Agda.Utils.Empty
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size (size)
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- * Tools for clauses

-- | Translate the clause patterns to terms with free variables bound by the
--   clause telescope.
--
--   Precondition: no projection patterns.
clauseArgs :: Clause -> Args
clauseArgs cl = fromMaybe __IMPOSSIBLE__ $ allApplyElims $ clauseElims cl

-- | Translate the clause patterns to an elimination spine
--   with free variables bound by the clause telescope.
clauseElims :: Clause -> Elims
clauseElims cl = patternsToElims $ namedClausePats cl

-- | Arity of a function, computed from clauses.
class FunArity a where
  funArity :: a -> Int

-- | Get the number of initial 'Apply' patterns.

#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPABLE #-} IsProjP p => FunArity [p] where
#else
instance IsProjP p => FunArity [p] where
#endif
  funArity = length . takeWhile (isNothing . isProjP)

-- | Get the number of initial 'Apply' patterns in a clause.
instance FunArity Clause where
  funArity = funArity . namedClausePats

-- | Get the number of common initial 'Apply' patterns in a list of clauses.
#if __GLASGOW_HASKELL__ >= 710
instance {-# OVERLAPPING #-} FunArity [Clause] where
#else
instance FunArity [Clause] where
#endif
  funArity []  = 0
  funArity cls = minimum $ map funArity cls

-- * Tools for patterns

-- | Label the pattern variables from left to right
--   using one label for each variable pattern and one for each dot pattern.
class LabelPatVars a b i | b -> i where
  labelPatVars :: a -> State [i] b
  unlabelPatVars :: b -> a
  -- ^ Intended, but unpractical due to the absence of type-level lambda, is:
  --   @labelPatVars :: f (Pattern' x) -> State [i] (f (Pattern' (i,x)))@

  default labelPatVars
    :: (Traversable f, LabelPatVars a' b' i, f a' ~ a, f b' ~ b)
    => a -> State [i] b
  labelPatVars = traverse labelPatVars

  default unlabelPatVars
    :: (Traversable f, LabelPatVars a' b' i, f a' ~ a, f b' ~ b)
    => b -> a
  unlabelPatVars = fmap unlabelPatVars

instance LabelPatVars a b i => LabelPatVars (Arg a) (Arg b) i         where
instance LabelPatVars a b i => LabelPatVars (Named x a) (Named x b) i where
instance LabelPatVars a b i => LabelPatVars [a] [b] i                 where

instance LabelPatVars Pattern DeBruijnPattern Int where
  labelPatVars p =
    case p of
      VarP x       -> do i <- next
                         return $ VarP (DBPatVar x i)
      DotP t       -> DotP t <$ next
      AbsurdP p    -> AbsurdP <$> labelPatVars p
      ConP c mt ps -> ConP c mt <$> labelPatVars ps
      LitP l       -> return $ LitP l
      ProjP o q    -> return $ ProjP o q
    where next = do (x:xs) <- get; put xs; return x
  unlabelPatVars = fmap dbPatVarName

-- | Augment pattern variables with their de Bruijn index.
{-# SPECIALIZE numberPatVars :: Int -> Permutation -> [NamedArg Pattern] -> [NamedArg DeBruijnPattern] #-}
--
--  Example:
--  @
--    f : (A : Set) (n : Nat) (v : Vec A n) -> ...
--    f A .(suc n) (cons n x xs)
--
--    clauseTel = (A : Set) (n : Nat) (x : A) (xs : Vec A n)
--    perm      = Perm 5 [0,2,3,4]
--    invertP __IMPOSSIBLE__ perm = Perm 4 [0,__IMPOSSIBLE__,1,2,3]
--    flipP ... = Perm 4 [3,__IMPOSSIBLE__,2,1,0]
--    pats      = A .(suc 2) (cons n x xs)
--    dBpats    = 3 .(suc 2) (cons 2 1 0 )
--  @
--
numberPatVars :: LabelPatVars a b Int => Int -> Permutation -> a -> b
numberPatVars err perm ps = evalState (labelPatVars ps) $
  permPicks $ flipP $ invertP err perm

unnumberPatVars :: LabelPatVars a b i => b -> a
unnumberPatVars = unlabelPatVars

dbPatPerm :: [NamedArg DeBruijnPattern] -> Maybe Permutation
dbPatPerm = dbPatPerm' True

-- | Computes the permutation from the clause telescope
--   to the pattern variables.
--
--   Use as @fromMaybe __IMPOSSIBLE__ . dbPatPerm@ to crash
--   in a controlled way if a de Bruijn index is out of scope here.
--
--   The first argument controls whether dot patterns counts as variables or
--   not.
dbPatPerm' :: Bool -> [NamedArg DeBruijnPattern] -> Maybe Permutation
dbPatPerm' countDots ps = Perm (size ixs) <$> picks
  where
    ixs   = concatMap (getIndices . namedThing . unArg) ps
    n     = size $ catMaybes ixs
    picks = forM (downFrom n) $ \ i -> List.findIndex (Just i ==) ixs

    getIndices :: DeBruijnPattern -> [Maybe Int]
    getIndices (VarP x)      = [Just $ dbPatVarIndex x]
    getIndices (ConP c _ ps) = concatMap (getIndices . namedThing . unArg) ps
    getIndices (DotP _)      = [Nothing | countDots]
    getIndices (AbsurdP p)   = getIndices p
    getIndices (LitP _)      = []
    getIndices ProjP{}       = []


-- | Computes the permutation from the clause telescope
--   to the pattern variables.
--
--   Use as @fromMaybe __IMPOSSIBLE__ . clausePerm@ to crash
--   in a controlled way if a de Bruijn index is out of scope here.
clausePerm :: Clause -> Maybe Permutation
clausePerm = dbPatPerm . namedClausePats

-- | Turn a pattern into a term.
--   Projection patterns are turned into projection eliminations,
--   other patterns into apply elimination.
patternToElim :: Arg DeBruijnPattern -> Elim
patternToElim (Arg ai (VarP x)) = Apply $ Arg ai $ var $ dbPatVarIndex x
patternToElim (Arg ai (ConP c cpi ps)) = Apply $ Arg ai $ Con c ci $
      map (argFromElim . patternToElim . fmap namedThing) ps
  where ci = fromConPatternInfo cpi
patternToElim (Arg ai (DotP t)     ) = Apply $ Arg ai t
patternToElim (Arg ai (AbsurdP p))   = patternToElim $ Arg ai p
patternToElim (Arg ai (LitP l)     ) = Apply $ Arg ai $ Lit l
patternToElim (Arg ai (ProjP o dest)) = Proj o dest

patternsToElims :: [NamedArg DeBruijnPattern] -> [Elim]
patternsToElims ps = map build ps
  where
    build :: NamedArg DeBruijnPattern -> Elim
    build = patternToElim . fmap namedThing

patternToTerm :: DeBruijnPattern -> Term
patternToTerm p = case patternToElim (defaultArg p) of
  Apply x -> unArg x
  Proj{}  -> __IMPOSSIBLE__


class MapNamedArg f where
  mapNamedArg :: (NamedArg a -> NamedArg b) -> NamedArg (f a) -> NamedArg (f b)

-- | Modify the content of @VarP@, and the closest surrounding @NamedArg@.
--
--   Note: the @mapNamedArg@ for @Pattern'@ is not expressible simply
--   by @fmap@ or @traverse@ etc., since @ConP@ has @NamedArg@ subpatterns,
--   which are taken into account by @mapNamedArg@.

instance MapNamedArg Pattern' where
  mapNamedArg f np =
    case namedArg np of
      VarP  x     -> updateNamedArg VarP $ f $ setNamedArg np x
      AbsurdP p   -> updateNamedArg AbsurdP $ mapNamedArg f $ setNamedArg np p
      DotP  t     -> setNamedArg np $ DotP t     -- just Haskell type conversion
      LitP  l     -> setNamedArg np $ LitP l     -- ditto
      ProjP o q   -> setNamedArg np $ ProjP o q  -- ditto
      ConP c i ps -> setNamedArg np $ ConP c i $ map (mapNamedArg f) ps


-- | Generic pattern traversal.
--
--   Pre-applies a pattern modification, recurses, and post-applies another one.

class PatternLike a b where

  -- | Fold pattern.
  foldrPattern
    :: Monoid m
    => (Pattern' a -> m -> m)
         -- ^ Combine a pattern and the value computed from its subpatterns.
    -> b -> m

  default foldrPattern
    :: (Monoid m, Foldable f, PatternLike a p, f p ~ b)
    => (Pattern' a -> m -> m) -> b -> m
  foldrPattern = foldMap . foldrPattern

  -- | Traverse pattern.
  traversePatternM :: (Monad m
#if __GLASGOW_HASKELL__ <= 708
    , Applicative m, Functor m
#endif
    ) => (Pattern' a -> m (Pattern' a))  -- ^ @pre@: Modification before recursion.
      -> (Pattern' a -> m (Pattern' a))  -- ^ @post@: Modification after recursion.
      -> b -> m b

  default traversePatternM :: (Traversable f, PatternLike a p, f p ~ b, Monad m
#if __GLASGOW_HASKELL__ <= 708
    , Applicative m, Functor m
#endif
    ) => (Pattern' a -> m (Pattern' a))
      -> (Pattern' a -> m (Pattern' a))
      -> b -> m b
  traversePatternM pre post = traverse $ traversePatternM pre post

-- | Compute from each subpattern a value and collect them all in a monoid.

foldPattern :: (PatternLike a b, Monoid m) => (Pattern' a -> m) -> b -> m
foldPattern f = foldrPattern $ \ p m -> f p `mappend` m

-- | Traverse pattern(s) with a modification before the recursive descent.

preTraversePatternM :: (PatternLike a b, Monad m
#if __GLASGOW_HASKELL__ <= 708
  , Applicative m, Functor m
#endif
  ) => (Pattern' a -> m (Pattern' a))  -- ^ @pre@: Modification before recursion.
    -> b -> m b
preTraversePatternM pre = traversePatternM pre return

-- | Traverse pattern(s) with a modification after the recursive descent.

postTraversePatternM :: (PatternLike a b, Monad m
#if __GLASGOW_HASKELL__ <= 708
  , Applicative m, Functor m
#endif
  ) => (Pattern' a -> m (Pattern' a))  -- ^ @post@: Modification after recursion.
    -> b -> m b
postTraversePatternM = traversePatternM return

-- This is where the action is:

instance PatternLike a (Pattern' a) where

  foldrPattern f p = f p $ case p of
    ConP _ _ ps -> foldrPattern f ps
    VarP _      -> mempty
    AbsurdP _   -> mempty
    LitP _      -> mempty
    DotP _      -> mempty
    ProjP _ _   -> mempty

  traversePatternM pre post = pre >=> recurse >=> post
    where
    recurse p = case p of
      ConP c ci ps -> ConP c ci <$> traversePatternM pre post ps
      VarP  _      -> return p
      LitP  _      -> return p
      DotP  _      -> return p
      AbsurdP _    -> return p
      ProjP _ _    -> return p

-- Boilerplate instances:

instance PatternLike a b => PatternLike a [b]         where
instance PatternLike a b => PatternLike a (Arg b)     where
instance PatternLike a b => PatternLike a (Named x b) where
