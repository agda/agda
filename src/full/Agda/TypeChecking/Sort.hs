{-# LANGUAGE ScopedTypeVariables #-}

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

import Data.Functor
import Data.Maybe

import Agda.Interaction.Options (optCumulativity)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import {-# SOURCE #-} Agda.TypeChecking.Constraints () -- instance only
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars () -- instance only

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.TypeChecking.Monad.Constraints (addConstraint, MonadConstraint)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.MetaVars (metaType)
import Agda.TypeChecking.Monad.Signature (HasConstInfo(..), applyDef)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.ProjectionLike (elimView)
import Agda.TypeChecking.Records (getDefType)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Except
import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Monad

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
  ifM (optCumulativity <$> pragmaOptions)
    (leqSort b' b)
    (equalSort b' b)

hasBiggerSort :: Sort -> TCM ()
hasBiggerSort = void . inferUnivSort

-- | Infer the sort of a pi type. If we can compute the sort straight away,
--   return that. Otherwise, return @PiSort a s2@ and add a constraint to
--   ensure we can compute the sort eventually.
inferPiSort
  :: (MonadReduce m, MonadAddContext m, MonadDebug m)
  => Dom Type -> Abs Sort -> m Sort
inferPiSort a s2 = do
  s1' <- reduce $ getSort a
  let a' = set lensSort s1' a
  s2' <- mapAbstraction a' reduce s2
  -- we do instantiateFull here to perhaps remove some (flexible)
  -- dependencies of s2 on var 0, thus allowing piSort' to reduce
  s2' <- instantiateFull s2'

  --Jesper, 2018-04-23: disabled PTS constraints for now,
  --this assumes that piSort can only be blocked by unsolved metas.

  --case piSort' s1 s2 of
  --  Just s -> return s
  --  Nothing -> do
  --    addConstraint $ HasPTSRule s1 s2
  --    return $ PiSort s1 s2

  return $ piSort a' s2'

-- | As @inferPiSort@, but for a nondependent function type.
inferFunSort :: Sort -> Sort -> TCM Sort
inferFunSort s1 s2 = funSort <$> reduce s1 <*> reduce s2

ptsRule :: Dom Type -> Abs Sort -> Sort -> TCM ()
ptsRule a b c = do
  c' <- inferPiSort a b
  ifM (optCumulativity <$> pragmaOptions)
    (leqSort c' c)
    (equalSort c' c)

-- | Non-dependent version of ptsRule
ptsRule' :: Sort -> Sort -> Sort -> TCM ()
ptsRule' a b c = do
  c' <- inferFunSort a b
  ifM (optCumulativity <$> pragmaOptions)
    (leqSort c' c)
    (equalSort c' c)

hasPTSRule :: Dom Type -> Abs Sort -> TCM ()
hasPTSRule a b = void $ inferPiSort a b

-- | Recursively check that an iterated function type constructed by @telePi@
--   is well-sorted.
checkTelePiSort :: Type -> TCM ()
-- Jesper, 2019-07-27: This is currently doing nothing (see comment in inferPiSort)
--checkTelePiSort (El s (Pi a b)) = do
--  -- Since the function type is assumed to be constructed by @telePi@,
--  -- we already know that @s == piSort (getSort a) (getSort <$> b)@,
--  -- so we just check that this sort is well-formed.
--  hasPTSRule a (getSort <$> b)
--  underAbstraction a b checkTelePiSort
checkTelePiSort _ = return ()

ifIsSort :: (MonadReduce m) => Type -> (Sort -> m a) -> m a -> m a
ifIsSort t yes no = do
  t <- reduce t
  case unEl t of
    Sort s -> yes s
    _      -> no

-- | Result is in reduced form.
shouldBeSort
  :: (MonadReduce m, MonadTCEnv m, ReadTCState m, MonadError TCErr m)
  => Type -> m Sort
shouldBeSort t = ifIsSort t return (typeError $ ShouldBeASort t)

-- | Reconstruct the sort of a type.
--
--   Precondition: given term is a well-sorted type.
sortOf
  :: forall m. (MonadReduce m, MonadTCEnv m, MonadAddContext m, HasBuiltins m, HasConstInfo m)
  => Term -> m Sort
sortOf t = do
  reportSDoc "tc.sort" 40 $ "sortOf" <+> prettyTCM t
  sortOfT =<< elimView True t

  where
    sortOfT :: Term -> m Sort
    sortOfT = \case
      Pi adom b -> do
        let a = unEl $ unDom adom
        sa <- sortOf a
        sb <- mapAbstraction adom (sortOf . unEl) b
        return $ piSort (adom $> El sa a) sb
      Sort s     -> do
        ui <- univInf
        return $ univSort ui s
      Var i es   -> do
        a <- typeOfBV i
        sortOfE a (Var i) es
      Def f es   -> do
        a <- defType <$> getConstInfo f
        sortOfE a (Def f) es
      MetaV x es -> do
        a <- metaType x
        sortOfE a (MetaV x) es
      Lam{}      -> __IMPOSSIBLE__
      Con{}      -> __IMPOSSIBLE__
      Lit{}      -> __IMPOSSIBLE__
      Level{}    -> __IMPOSSIBLE__
      DontCare{} -> __IMPOSSIBLE__
      Dummy s _  -> __IMPOSSIBLE_VERBOSE__ s

    sortOfE :: Type -> (Elims -> Term) -> Elims -> m Sort
    sortOfE a hd []     = ifIsSort a return __IMPOSSIBLE__
    sortOfE a hd (e:es) = case e of
      Apply (Arg ai v) -> ifNotPiType a __IMPOSSIBLE__ $ \b c -> do
        sortOfE (c `absApp` v) (hd . (e:)) es
      Proj o f -> do
        a <- reduce a
        ~(El _ (Pi b c)) <- fromMaybe __IMPOSSIBLE__ <$> getDefType f a
        hd' <- applyE <$> applyDef o f (argFromDom b $> hd [])
        sortOfE (c `absApp` (hd [])) hd' es
      IApply x y r -> do
        (b , c) <- fromMaybe __IMPOSSIBLE__ <$> isPath a
        sortOfE (c `absApp` r) (hd . (e:)) es
