{-# OPTIONS_GHC -Wunused-imports #-}

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

import {-# SOURCE #-} Agda.TypeChecking.Constraints () -- instance only
import {-# SOURCE #-} Agda.TypeChecking.Conversion
import {-# SOURCE #-} Agda.TypeChecking.MetaVars () -- instance only

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints (addConstraint, MonadConstraint)
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.MetaVars (metaType)
import Agda.TypeChecking.Monad.Options ( isLevelUniverseEnabled )
import Agda.TypeChecking.Monad.Pure
import Agda.TypeChecking.Monad.Signature (HasConstInfo(..), applyDef)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records (getDefType)
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Monad

import Agda.Utils.Impossible

{-# SPECIALIZE inferUnivSort :: Sort -> TCM Sort #-}
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

{-# SPECIALIZE sortFitsIn :: Sort -> Sort -> TCM () #-}
sortFitsIn :: MonadConversion m => Sort -> Sort -> m ()
sortFitsIn a b = do
  b' <- inferUnivSort a
  ifM (optCumulativity <$> pragmaOptions)
    (leqSort b' b)
    (equalSort b' b)

hasBiggerSort :: Sort -> TCM ()
hasBiggerSort = void . inferUnivSort

{-# SPECIALIZE inferPiSort :: Dom Type -> Abs Type -> TCM Sort #-}
-- | Infer the sort of a Pi type.
--   If we can compute the sort straight away, return that.
--   Otherwise, return a 'PiSort'.
--   Note that this function does NOT check PTS constraints, use 'hasPTSRule' for that
inferPiSort :: (PureTCM m, MonadConstraint m)
  => Dom Type  -- ^ Domain of the Pi type.
  -> Abs Type  -- ^ (Dependent) codomain of the Pi type.
  -> m Sort    -- ^ Sort of the Pi type.
inferPiSort a b = piSortM (unEl <$> a) (getSort a) (getSort <$> b)

{-# SPECIALIZE inferFunSort :: Dom Type -> Type -> TCM Sort #-}
-- | As @inferPiSort@, but for a nondependent function type.
--
inferFunSort :: (PureTCM m, MonadConstraint m)
  => Dom Type  -- ^ Domain of the function type.
  -> Type      -- ^ Sort of the codomain of the function type.
  -> m Sort    -- ^ Sort of the function type.
inferFunSort a b = funSortM (getSort a) (getSort b)

-- | @hasPTSRule a x.s@ checks that we can form a Pi-type @(x : a) -> b@ where @b : s@.
--
hasPTSRule :: Dom Type -> Abs Sort -> TCM ()
hasPTSRule a s = do
  reportSDoc "tc.conv.sort" 35 $ vcat
    [ "hasPTSRule"
    , "a =" <+> prettyTCM a
    , "s =" <+> underAbstraction a s prettyTCM
    ]
  -- If @LevelUniv@ is disabled then all pi sorts are valid.
  hasLevelUniv <- isLevelUniverseEnabled
  if not hasLevelUniv || alwaysValidCodomain (unAbs s)
  then yes
  else do
    sb <- reduceB =<< piSortM (unEl <$> a) (getSort a) s
    case sb of
      Blocked b t | neverUnblock == b -> no sb t
                  | otherwise         -> postpone b
      NotBlocked _ t@FunSort{}        -> no sb t
      NotBlocked _ t@PiSort{}         -> no sb t
      NotBlocked{}                    -> yes
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
    postpone b = addConstraint b $ HasPTSRule a s

-- | Recursively check that an iterated function type constructed by @telePi@
--   is well-sorted.
checkTelePiSort :: Telescope -> Sort -> TCM ()
checkTelePiSort tel s = void $ loop tel
  where
    loop :: Telescope -> TCM Sort
    loop EmptyTel = return s
    loop (ExtendTel a atel) = do
      s' <- mapAbstraction a loop atel
      hasPTSRule a s'
      piSortM (unEl <$> a) (getSort $ unDom a) s'

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

{-# SPECIALIZE ifNotSort :: Type -> TCM a -> (Sort -> TCM a) -> TCM a #-}
ifNotSort :: (MonadReduce m, MonadBlock m) => Type -> m a -> (Sort -> m a) -> m a
ifNotSort t = flip $ ifIsSort t

{-# SPECIALIZE shouldBeSort :: Type -> TCM Sort #-}
-- | Result is in reduced form.
shouldBeSort
  :: (PureTCM m, MonadBlock m, MonadError TCErr m)
  => Type -> m Sort
shouldBeSort t = ifIsSort t return (typeError $ ShouldBeASort t)

{-# SPECIALIZE sortOf :: Term -> TCM Sort #-}
-- | Reconstruct the sort of a term.
--
--   Precondition: given term is a well-sorted type.
sortOf
  :: forall m. (PureTCM m, MonadBlock m, MonadConstraint m)
  => Term -> m Sort
sortOf t = do
  reportSDoc "tc.sort" 60 $ "sortOf" <+> prettyTCM t
  sortOfT =<< elimView EvenLone t

  where
    sortOfT :: Term -> m Sort
    sortOfT = \case
      Pi adom b -> do
        sa <- sortOf $ unEl $ unDom adom
        sb <- mapAbstraction adom (sortOf . unEl) b
        piSortM (unEl <$> adom) sa sb
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

      ba <- reduceB a

      let
        a' = ignoreBlocking ba
        fallback = case ba of
          Blocked m _ -> patternViolation m

          -- Not IMPOSSIBLE because of possible non-confluent rewriting (see #5531)
          _ -> ifM (optRewriting <$> pragmaOptions)
            {-then-} (patternViolation neverUnblock)
            {-else-} __IMPOSSIBLE__

      case e of
        Apply (Arg ai v) -> case unEl a' of
          Pi b c -> sortOfE (c `absApp` v) (hd . (e:)) es
          _ -> fallback

        Proj o f -> case unEl a' of
          Def{} -> do
            ~(El _ (Pi b c)) <- fromMaybe __IMPOSSIBLE__ <$> getDefType f a'
            hd' <- applyE <$> applyDef o f (argFromDom b $> hd [])
            sortOfE (c `absApp` (hd [])) hd' es
          _ -> fallback

        IApply x y r -> do
          (b , c) <- fromMaybe __IMPOSSIBLE__ <$> isPath a'
          sortOfE (c `absApp` r) (hd . (e:)) es

{-# INLINE sortOfType #-}
-- | Reconstruct the minimal sort of a type (ignoring the sort annotation).
sortOfType
  :: forall m. (PureTCM m, MonadBlock m,MonadConstraint m)
  => Type -> m Sort
sortOfType = sortOf . unEl
