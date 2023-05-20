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
import Control.Monad.Except

import Data.Functor
import Data.Maybe

import Agda.Interaction.Options (optCumulativity, optRewriting)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars

import {-# SOURCE #-} Agda.TypeChecking.Constraints () -- instance only
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars () -- instance only

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin (HasBuiltins)
import Agda.TypeChecking.Monad.Constraints (addConstraint, MonadConstraint)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.MetaVars (metaType)
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Signature (HasConstInfo(..), applyDef)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records (getDefType)
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Monad

-- | Infer the sort of another sort. If we can compute the bigger sort
--   straight away, return that. Otherwise, return @UnivSort s@ and add a
--   constraint to ensure we can compute the sort eventually.
inferUnivSort
  :: (PureTCM m, MonadConstraint m)
  => Sort -> m Sort
inferUnivSort s = do
  s <- reduce s
  case univSort' s of
    Right s' -> return s'
    Left _ -> do
      -- Jesper, 2020-04-19: With the addition of Setωᵢ and the PTS
      -- rule SizeUniv : Setω, every sort (with no metas) now has a
      -- bigger sort, so we do not need to add a constraint.
      -- addConstraint $ HasBiggerSort s
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
inferPiSort :: (PureTCM m,MonadConstraint m) => Dom Type -> Abs Sort -> m Sort
inferPiSort a s2 = do
  s1' <- reduceB $ getSort a
  s2' <- mapAbstraction a reduceB s2
  --Jesper, 2018-04-23: disabled PTS constraints for now,
  --this assumes that piSort can only be blocked by unsolved metas.
  --Arthur Adjedj, 2023-02-27, Turned PTS back on,
  --piSort can now be blocked by Leveluniv
  let b' = unblockOnEither (getBlocker s1') (getBlocker $ unAbs s2')
  case piSort' (unEl <$> a) (ignoreBlocking s1') (ignoreBlocking <$> s2') of
    Right s -> return s
    Left b -> do
      addConstraint (unblockOnEither b b') $ HasPTSRule a (ignoreBlocking <$> s2')
      return $ PiSort (unEl <$> a) (ignoreBlocking s1') (ignoreBlocking <$> s2')


-- | As @inferPiSort@, but for a nondependent function type.
inferFunSort :: Dom Type -> Sort -> TCM Sort
inferFunSort a s2 = do
  let s1 = getSort a
  s1' <- reduceB s1
  s2' <- reduceB s2
  case funSort' (ignoreBlocking s1') (ignoreBlocking s2') of
    Right s -> return s
    Left b -> do
      let b' = unblockOnEither (getBlocker s1') (getBlocker s2')
      addConstraint (unblockOnEither b b') $ HasPTSRule a (NoAbs "_" $ ignoreBlocking s2')
      return $ FunSort s1 s2

-- | @hasPTSRule a x.s@ checks that we can form a Pi-type @(x : a) -> b@ where @b : s@.
--
hasPTSRule :: Dom Type -> Abs Sort -> TCM ()
hasPTSRule a s = do
  reportSDoc "tc.conv.sort" 35 $ vcat
    [ "hasPTSRule"
    , "a =" <+> prettyTCM a
    , "s =" <+> prettyTCM (unAbs s)
    ]
  if alwaysValidCodomain $ unAbs s
  then yes
  else do
    sb <- reduceB =<< inferPiSort a s
    case sb of
      Blocked b t | neverUnblock == b -> no sb t
      NotBlocked _ t@FunSort{}        -> no sb t
      NotBlocked _ t@PiSort{}         -> no sb t
      _ -> yes
  where
    -- Do we end in a standard sort (Prop, Type, SSet)?
    alwaysValidCodomain = \case
      Inf{} -> True
      Univ{} -> True
      FunSort _ s -> alwaysValidCodomain s
      PiSort _ _ s -> alwaysValidCodomain $ unAbs s
      _ -> False

    yes = do
      reportSLn "tc.conv.sort" 35 "hasPTSRule succeeded"
    no sb t = do
      reportSDoc "tc.conv.sort" 35 $ "hasPTSRule fails on" <+> prettyTCM sb
      typeError $ InvalidTypeSort t

-- | Recursively check that an iterated function type constructed by @telePi@
--   is well-sorted.
checkTelePiSort :: Type -> TCM ()
-- Jesper, 2019-07-27: This is currently doing nothing (see comment in inferPiSort)
checkTelePiSort (El s (Pi a b)) = do
  -- Since the function type is assumed to be constructed by @telePi@,
  -- we already know that @s == piSort (getSort a) (getSort <$> b)@,
  -- so we just check that this sort is well-formed.
  hasPTSRule a (getSort <$> b)
  underAbstraction a b checkTelePiSort
checkTelePiSort _ = return ()

ifIsSort :: (MonadReduce m, MonadBlock m) => Type -> (Sort -> m a) -> m a -> m a
ifIsSort t yes no = do
  -- Jesper, 2020-09-06, subtle: do not use @abortIfBlocked@ here
  -- since we want to take the yes branch whenever the type is a sort,
  -- even if it is blocked.
  bt <- reduceB t
  case unEl (ignoreBlocking bt) of
    Sort s                     -> yes s
    _      | Blocked m _ <- bt -> patternViolation m
           | otherwise         -> no

ifNotSort :: (MonadReduce m, MonadBlock m) => Type -> m a -> (Sort -> m a) -> m a
ifNotSort t = flip $ ifIsSort t

-- | Result is in reduced form.
shouldBeSort
  :: (PureTCM m, MonadBlock m, MonadError TCErr m)
  => Type -> m Sort
shouldBeSort t = ifIsSort t return (typeError $ ShouldBeASort t)

-- | Reconstruct the sort of a term.
--
--   Precondition: given term is a well-sorted type.
sortOf
  :: forall m. (PureTCM m, MonadBlock m,MonadConstraint m)
  => Term -> m Sort
sortOf t = do
  reportSDoc "tc.sort" 60 $ "sortOf" <+> prettyTCM t
  sortOfT =<< elimView EvenLone t

  where
    sortOfT :: Term -> m Sort
    sortOfT = \case
      Pi adom b -> do
        let a = unEl $ unDom adom
        sa <- sortOf a
        sb <- mapAbstraction adom (sortOf . unEl) b
        inferPiSort (adom $> El sa a) sb
      Sort s     -> return $ univSort s
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
    sortOfE a hd (e:es) = do
     reportSDoc "tc.sort" 50 $ vcat
       [ "sortOfE"
       , "  a  = " <+> prettyTCM a
       , "  hd = " <+> prettyTCM (hd [])
       , "  e  = " <+> prettyTCM e
       ]
     case e of
      Apply (Arg ai v) -> do
        ba <- reduceB a
        case unEl (ignoreBlocking ba) of
          Pi b c -> sortOfE (c `absApp` v) (hd . (e:)) es
          _ | Blocked m _ <- ba -> patternViolation m
            | otherwise         -> ifM (optRewriting <$> pragmaOptions)
                {-then-} (patternViolation neverUnblock)  -- Not IMPOSSIBLE because of possible non-confluent rewriting (see #5531)
                {-else-} __IMPOSSIBLE__
      Proj o f -> do
        a <- reduce a
        ~(El _ (Pi b c)) <- fromMaybe __IMPOSSIBLE__ <$> getDefType f a
        hd' <- applyE <$> applyDef o f (argFromDom b $> hd [])
        sortOfE (c `absApp` (hd [])) hd' es
      IApply x y r -> do
        (b , c) <- fromMaybe __IMPOSSIBLE__ <$> isPath a
        sortOfE (c `absApp` r) (hd . (e:)) es

-- | Reconstruct the minimal sort of a type (ignoring the sort annotation).
sortOfType
  :: forall m. (PureTCM m, MonadBlock m,MonadConstraint m)
  => Type -> m Sort
sortOfType = sortOf . unEl
