{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE UndecidableInstances   #-}  -- because of func. deps.

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

module Agda.Syntax.Internal.Pattern where

import Control.Applicative
import Control.Monad.State

import Data.Maybe
import Data.List
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Abstract (IsProjP(..))
import Agda.Syntax.Internal
import qualified Agda.Syntax.Internal as I

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
  funArity = funArity . clausePats

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

instance LabelPatVars a b i => LabelPatVars (Arg a) (Arg b) i where
  labelPatVars = traverse labelPatVars
  unlabelPatVars = fmap unlabelPatVars

instance LabelPatVars a b i => LabelPatVars (Named x a) (Named x b) i where
  labelPatVars = traverse labelPatVars
  unlabelPatVars = fmap unlabelPatVars

instance LabelPatVars a b i => LabelPatVars [a] [b] i where
  labelPatVars = traverse labelPatVars
  unlabelPatVars = fmap unlabelPatVars

instance LabelPatVars (Pattern' x) (Pattern' (i,x)) i where
  labelPatVars p =
    case p of
      VarP x       -> VarP . (,x) <$> next
      DotP t       -> DotP t <$ next
      ConP c mt ps -> ConP c mt <$> labelPatVars ps
      LitP l       -> return $ LitP l
      ProjP q      -> return $ ProjP q
    where next = do (x:xs) <- get; put xs; return x
  unlabelPatVars = fmap snd

-- | Augment pattern variables with their de Bruijn index.
{-# SPECIALIZE numberPatVars :: Permutation -> [NamedArg (Pattern' x)] -> [NamedArg (Pattern' (Int, x))] #-}
{-# SPECIALIZE numberPatVars :: Permutation -> [NamedArg Pattern] -> [NamedArg DeBruijnPattern] #-}
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
numberPatVars :: LabelPatVars a b Int => Permutation -> a -> b
numberPatVars perm ps = evalState (labelPatVars ps) $
  permPicks $ flipP $ invertP __IMPOSSIBLE__ perm

unnumberPatVars :: LabelPatVars a b i => b -> a
unnumberPatVars = unlabelPatVars

dbPatPerm :: [NamedArg DeBruijnPattern] -> Permutation
dbPatPerm ps = Perm (size ixs) picks
  where
    ixs   = concatMap (getIndices . namedThing . unArg) ps
    n     = size $ catMaybes ixs
    picks = for (downFrom n) $ \i ->
      fromMaybe __IMPOSSIBLE__ $ findIndex (Just i ==) ixs

    getIndices :: DeBruijnPattern -> [Maybe Int]
    getIndices (VarP (i,_))  = [Just i]
    getIndices (ConP c _ ps) = concatMap (getIndices . namedThing . unArg) ps
    getIndices (DotP _)      = [Nothing]
    getIndices (LitP _)      = []
    getIndices (ProjP _)     = []

clausePerm :: Clause -> Permutation
clausePerm = dbPatPerm . namedClausePats

patternToElim :: Arg DeBruijnPattern -> Elim
patternToElim (Arg ai (VarP (i, _))) = Apply $ Arg ai $ var i
patternToElim (Arg ai (ConP c _ ps)) = Apply $ Arg ai $ Con c $
      map (argFromElim . patternToElim . fmap namedThing) ps
patternToElim (Arg ai (DotP t)     ) = Apply $ Arg ai t
patternToElim (Arg ai (LitP l)     ) = Apply $ Arg ai $ Lit l
patternToElim (Arg ai (ProjP dest) ) = Proj  $ dest

patternsToElims :: [NamedArg DeBruijnPattern] -> [Elim]
patternsToElims ps = map build ps
  where
    build :: NamedArg DeBruijnPattern -> Elim
    build = patternToElim . fmap namedThing

patternToTerm :: DeBruijnPattern -> Term
patternToTerm p = case patternToElim (defaultArg p) of
  Apply x -> unArg x
  Proj  f -> __IMPOSSIBLE__

-- patternsToElims :: Permutation -> [NamedArg Pattern] -> [Elim]
-- patternsToElims perm ps = evalState (mapM build' ps) xs
--   where
--     xs   = permute (invertP __IMPOSSIBLE__ perm) $ downFrom (size perm)

--     tick :: State [Int] Int
--     tick = do x : xs <- get; put xs; return x

--     build' :: NamedArg Pattern -> State [Int] Elim
--     build' = build . fmap namedThing

--     build :: Arg Pattern -> State [Int] Elim
--     build (Arg ai (VarP _)     ) = Apply . Arg ai . var <$> tick
--     build (Arg ai (ConP c _ ps)) =
--       Apply . Arg ai . Con c <$> mapM (argFromElim <.> build') ps
--     build (Arg ai (DotP t)     ) = Apply (Arg ai t) <$ tick
--     build (Arg ai (LitP l)     ) = return $ Apply $ Arg ai $ Lit l
--     build (Arg ai (ProjP dest) ) = return $ Proj  $ dest
