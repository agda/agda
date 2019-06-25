
-- | This module contains the rules for Agda's sort system viewed as a pure
--   type system (pts). The specification of a pts consists of a set
--   of axioms of the form @s1 : s2@ specifying when a sort fits in
--   another sort, and a set of rules of the form @(s1,s2,s3)@
--   specifying that a pi type with domain in @s1@ and codomain in
--   @s2@ itself fits into sort @s3@.
--
--   To ensure unique principal types, the axioms and rules of Agda's
--   pts are given by two partial functions @univSort'@ and @piSort'@
--   (see @Agda.TypeChecking.Substitute@). If these functions return
--   @Nothing@, a constraint is added to ensure that the sort will be
--   computed eventually.
--
--   One 'upgrade' over the standard definition of a pts is that in a
--   rule @(s1,s2,s3)@, in Agda the sort @s2@ can depend on a variable
--   of some type in @s1@. This is needed to support Agda's universe
--   polymorphism where we can have e.g. a function of type @∀ {ℓ} →
--   Set ℓ@.

module Agda.TypeChecking.Sort where

import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal

import {-# SOURCE #-} Agda.TypeChecking.Constraints ()
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars

import Agda.TypeChecking.Free
import Agda.TypeChecking.Irrelevance
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints (addConstraint, MonadConstraint)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute

import Agda.Utils.Impossible

-- | Infer the sort of another sort. If we can compute the bigger sort
--   straight away, return that. Otherwise, return @UnivSort s@ and add a
--   constraint to ensure we can compute the sort eventually.
inferUnivSort
  :: (MonadReduce m, MonadConstraint m, HasOptions m)
  => Sort -> m Sort
inferUnivSort s = do
  s <- reduce s
  ui <- univInf
  case univSort' ui s of
    Just s' -> return s'
    Nothing -> do
      addConstraint $ HasBiggerSort s
      return $ UnivSort s

sortFitsIn :: MonadConversion m => Sort -> Sort -> m ()
sortFitsIn a b = do
  b' <- inferUnivSort a
  equalSort b' b -- CUMULATIVITY: leqSort b' b

hasBiggerSort :: Sort -> TCM ()
hasBiggerSort = void . inferUnivSort

-- | Infer the sort of a pi type. If we can compute the sort straight away,
--   return that. Otherwise, return @PiSort s1 s2@ and add a constraint to
--   ensure we can compute the sort eventually.
inferPiSort :: MonadReduce m => Sort -> Abs Sort -> m Sort
inferPiSort s1 s2 = do
  (s1,s2) <- reduce (s1,s2)
  -- we do instantiateFull here to perhaps remove some (flexible)
  -- dependencies of s2 on var 0, thus allowing piSort' to reduce
  s2 <- instantiateFull s2

  --Jesper, 2018-04-23: disabled PTS constraints for now,
  --this assumes that piSort can only be blocked by unsolved metas.

  --case piSort' s1 s2 of
  --  Just s -> return s
  --  Nothing -> do
  --    addConstraint $ HasPTSRule s1 s2
  --    return $ PiSort s1 s2

  return $ piSort s1 s2

-- | As @inferPiSort@, but for a nondependent function type.
inferFunSort :: Sort -> Sort -> TCM Sort
inferFunSort s1 s2 = inferPiSort s1 $ NoAbs underscore s2

ptsRule :: Sort -> Abs Sort -> Sort -> TCM ()
ptsRule a b c = do
  c' <- inferPiSort a b
  equalSort c' c -- CUMULATIVITY: leqSort c' c

-- | Non-dependent version of ptsRule
ptsRule' :: Sort -> Sort -> Sort -> TCM ()
ptsRule' a b c = do
  c' <- inferFunSort a b
  equalSort c' c -- CUMULATIVITY: leqSort c' c

hasPTSRule :: Sort -> Abs Sort -> TCM ()
hasPTSRule a b = void $ inferPiSort a b

-- | Recursively check that an iterated function type constructed by @telePi@
--   is well-sorted.
checkTelePiSort :: Type -> TCM ()
checkTelePiSort (El s (Pi a b)) = do
  -- Since the function type is assumed to be constructed by @telePi@,
  -- we already know that @s == piSort (getSort a) (getSort <$> b)@,
  -- so we just check that this sort is well-formed.
  hasPTSRule (getSort a) (getSort <$> b)
  underAbstraction a b checkTelePiSort
checkTelePiSort _ = return ()

ifIsSort :: (MonadReduce m) => Type -> (Sort -> m a) -> m a -> m a
ifIsSort t yes no = do
  t <- reduce t
  case unEl t of
    Sort s -> yes s
    _      -> no
