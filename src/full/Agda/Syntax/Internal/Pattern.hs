{-# LANGUAGE TypeFamilies           #-}  -- because of type equality ~
{-# LANGUAGE UndecidableInstances   #-}  -- because of func. deps.

module Agda.Syntax.Internal.Pattern where

import Control.Arrow (second)
import Control.Monad.State

import Data.Maybe
import Data.Monoid
import qualified Data.List as List

import Agda.Syntax.Common
import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Internal

import Agda.Utils.List
import Agda.Utils.Permutation
import Agda.Utils.Size (size)

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

instance {-# OVERLAPPABLE #-} IsProjP p => FunArity [p] where
  funArity = length . takeWhile (isNothing . isProjP)

-- | Get the number of initial 'Apply' patterns in a clause.
instance FunArity Clause where
  funArity = funArity . namedClausePats

-- | Get the number of common initial 'Apply' patterns in a list of clauses.
instance {-# OVERLAPPING #-} FunArity [Clause] where
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
      VarP o x     -> do i <- next
                         return $ VarP o (DBPatVar x i)
      DotP o t     -> DotP o t <$ next
      ConP c mt ps -> ConP c mt <$> labelPatVars ps
      DefP o q ps -> DefP o q <$> labelPatVars ps
      LitP o l     -> return $ LitP o l
      ProjP o q    -> return $ ProjP o q
      IApplyP o u t x -> do i <- next
                            return $ IApplyP o u t (DBPatVar x i)
    where next = caseListM get __IMPOSSIBLE__ $ \ x xs -> do put xs; return x
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
    getIndices (VarP _ x)    = [Just $ dbPatVarIndex x]
    getIndices (ConP c _ ps) = concatMap (getIndices . namedThing . unArg) ps
    getIndices (DefP _ _ ps) = concatMap (getIndices . namedThing . unArg) ps
    getIndices (DotP _ _)    = [Nothing | countDots]
    getIndices (LitP _ _)    = []
    getIndices ProjP{}       = []
    getIndices (IApplyP _ _ _ x) = [Just $ dbPatVarIndex x]

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
patternToElim (Arg ai (VarP o x)) = Apply $ Arg ai $ var $ dbPatVarIndex x
patternToElim (Arg ai (ConP c cpi ps)) = Apply $ Arg ai $ Con c ci $
      map (patternToElim . fmap namedThing) ps
  where ci = fromConPatternInfo cpi
patternToElim (Arg ai (DefP o q ps)) = Apply $ Arg ai $ Def q $
      map (patternToElim . fmap namedThing) ps
patternToElim (Arg ai (DotP o t)   ) = Apply $ Arg ai t
patternToElim (Arg ai (LitP o l)    ) = Apply $ Arg ai $ Lit l
patternToElim (Arg ai (ProjP o dest)) = Proj o dest
patternToElim (Arg ai (IApplyP o t u x)) = IApply t u $ var $ dbPatVarIndex x

patternsToElims :: [NamedArg DeBruijnPattern] -> [Elim]
patternsToElims ps = map build ps
  where
    build :: NamedArg DeBruijnPattern -> Elim
    build = patternToElim . fmap namedThing

patternToTerm :: DeBruijnPattern -> Term
patternToTerm p = case patternToElim (defaultArg p) of
  Apply x -> unArg x
  Proj{}  -> __IMPOSSIBLE__
  IApply _ _ x -> x


class MapNamedArgPattern a p where
  mapNamedArgPattern :: (NamedArg (Pattern' a) -> NamedArg (Pattern' a)) -> p -> p

  default mapNamedArgPattern
    :: (Functor f, MapNamedArgPattern a p', p ~ f p')
    => (NamedArg (Pattern' a) -> NamedArg (Pattern' a)) -> p -> p
  mapNamedArgPattern = fmap . mapNamedArgPattern

-- | Modify the content of @VarP@, and the closest surrounding @NamedArg@.
--
--   Note: the @mapNamedArg@ for @Pattern'@ is not expressible simply
--   by @fmap@ or @traverse@ etc., since @ConP@ has @NamedArg@ subpatterns,
--   which are taken into account by @mapNamedArg@.

instance MapNamedArgPattern a (NamedArg (Pattern' a)) where
  mapNamedArgPattern f np =
    case namedArg np of
      VarP o x    -> f np
      DotP  o t   -> f np
      LitP o l    -> f np
      ProjP o q   -> f np
      ConP c i ps -> f $ setNamedArg np $ ConP c i $ mapNamedArgPattern f ps
      DefP o q ps -> f $ setNamedArg np $ DefP o q $ mapNamedArgPattern f ps
      IApplyP o u t x -> f np

instance MapNamedArgPattern a p => MapNamedArgPattern a [p] where


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
  traversePatternM
    :: Monad m
    => (Pattern' a -> m (Pattern' a))  -- ^ @pre@: Modification before recursion.
    -> (Pattern' a -> m (Pattern' a))  -- ^ @post@: Modification after recursion.
    -> b -> m b

  default traversePatternM
    :: (Traversable f, PatternLike a p, f p ~ b, Monad m)
    => (Pattern' a -> m (Pattern' a))
    -> (Pattern' a -> m (Pattern' a))
    -> b -> m b

  traversePatternM pre post = traverse $ traversePatternM pre post

-- | Compute from each subpattern a value and collect them all in a monoid.

foldPattern :: (PatternLike a b, Monoid m) => (Pattern' a -> m) -> b -> m
foldPattern f = foldrPattern $ \ p m -> f p `mappend` m

-- | Traverse pattern(s) with a modification before the recursive descent.

preTraversePatternM
  :: (PatternLike a b, Monad m)
  => (Pattern' a -> m (Pattern' a))  -- ^ @pre@: Modification before recursion.
  -> b -> m b
preTraversePatternM pre = traversePatternM pre return

-- | Traverse pattern(s) with a modification after the recursive descent.

postTraversePatternM :: (PatternLike a b, Monad m)
                     => (Pattern' a -> m (Pattern' a))  -- ^ @post@: Modification after recursion.
                     -> b -> m b
postTraversePatternM = traversePatternM return

-- This is where the action is:

instance PatternLike a (Pattern' a) where

  foldrPattern f p = f p $ case p of
    ConP _ _ ps -> foldrPattern f ps
    DefP _ _ ps -> foldrPattern f ps
    VarP _ _    -> mempty
    LitP _ _    -> mempty
    DotP _ _    -> mempty
    ProjP _ _   -> mempty
    IApplyP{}   -> mempty

  traversePatternM pre post = pre >=> recurse >=> post
    where
    recurse p = case p of
      ConP c ci ps -> ConP c ci <$> traversePatternM pre post ps
      DefP o q ps  -> DefP o q <$> traversePatternM pre post ps
      VarP  _ _    -> return p
      LitP  _ _    -> return p
      DotP  _ _    -> return p
      ProjP _ _    -> return p
      IApplyP{}    -> return p

-- Boilerplate instances:

instance PatternLike a b => PatternLike a [b]         where
instance PatternLike a b => PatternLike a (Arg b)     where
instance PatternLike a b => PatternLike a (Named x b) where

-- Counting pattern variables ---------------------------------------------

class CountPatternVars a where
  countPatternVars :: a -> Int

  default countPatternVars :: (Foldable f, CountPatternVars b, f b ~ a) =>
                              a -> Int
  countPatternVars = getSum . foldMap (Sum . countPatternVars)

instance CountPatternVars a => CountPatternVars [a] where
instance CountPatternVars a => CountPatternVars (Arg a) where
instance CountPatternVars a => CountPatternVars (Named x a) where

instance CountPatternVars (Pattern' x) where
  countPatternVars p =
    case p of
      VarP{}      -> 1
      ConP _ _ ps -> countPatternVars ps
      DotP{}      -> 1   -- dot patterns are treated as variables in the clauses
      _           -> 0

-- Computing modalities of pattern variables ------------------------------

class PatternVarModalities p x | p -> x where
  -- | Get the list of pattern variables annotated with modalities.
  patternVarModalities :: p -> [(x, Modality)]

instance PatternVarModalities a x => PatternVarModalities [a] x where
  patternVarModalities = foldMap patternVarModalities

instance PatternVarModalities a x => PatternVarModalities (Named s a) x where
  patternVarModalities = foldMap patternVarModalities

instance PatternVarModalities a x => PatternVarModalities (Arg a) x where
  patternVarModalities arg = map (second (m <>)) (patternVarModalities $ unArg arg)
    where m = getModality arg

-- UNUSED:
-- instance PatternVarModalities a x => PatternVarModalities (Elim' a) x where
--   patternVarModalities (Apply x) = patternVarModalities x -- Note: x :: Arg a
--   patternVarModalities (IApply x y p) = patternVarModalities [x, y, p]
--   patternVarModalities Proj{}    = []

instance PatternVarModalities (Pattern' x) x where
  patternVarModalities p =
    case p of
      VarP _ x    -> [(x, defaultModality)]
      ConP _ _ ps -> patternVarModalities ps
      DefP _ _ ps -> patternVarModalities ps
      DotP{}      -> []
      LitP{}      -> []
      ProjP{}     -> []
      IApplyP _ _ _ x -> [(x, defaultModality)]
