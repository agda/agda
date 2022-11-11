{-# OPTIONS_GHC -Wunused-imports #-}

{- | Modality.

Agda has support for several modalities, namely:

 * 'Cohesion'
 * 'Quantity'
 * 'Relevance'

In order to type check such modalities, we must store the current modality in
the typing context. This module provides functions to update the context based
on a given modality.

See "Agda.TypeChecking.Irrelevance".
-}

module Agda.TypeChecking.Monad.Modality where

import qualified Data.Map as Map

import Agda.Interaction.Options

import Agda.Syntax.Common

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Env

import Agda.Utils.Function
import Agda.Utils.Lens
import Agda.Utils.Monad

-- | data 'Relevance'
--   see "Agda.Syntax.Common".

-- * Operations on 'Dom'.

-- | Prepare parts of a parameter telescope for abstraction in constructors
--   and projections.
hideAndRelParams :: (LensHiding a, LensRelevance a) => a -> a
hideAndRelParams = hideOrKeepInstance . mapRelevance shapeIrrelevantToIrrelevant

-- * Operations on 'Context'.

-- | Modify the context whenever going from the l.h.s. (term side)
--   of the typing judgement to the r.h.s. (type side).
workOnTypes :: (MonadTCEnv m, HasOptions m, MonadDebug m)
            => m a -> m a
workOnTypes cont = do
  allowed <- optExperimentalIrrelevance <$> pragmaOptions
  verboseBracket "tc.irr" 60 "workOnTypes" $ workOnTypes' allowed cont

-- | Internal workhorse, expects value of --experimental-irrelevance flag
--   as argument.
workOnTypes' :: (MonadTCEnv m) => Bool -> m a -> m a
workOnTypes' experimental
  = applyWhen experimental (modifyContextInfo $ mapRelevance irrelevantToShapeIrrelevant)
  . applyQuantityToJudgement zeroQuantity
  . applyPolarityToContext (withStandardLock UnusedPolarity)
  . typeLevelReductions
  . localTC (\ e -> e { envWorkingOnTypes = True })

applyPolarityToContext :: (MonadTCEnv tcm, LensModalPolarity p) => p -> tcm a -> tcm a
applyPolarityToContext p = localTC
  $ over eContext     (map $ inverseApplyPolarity pol)
  . over eLetBindings (Map.map . fmap . onLetBindingType
                       $ inverseApplyPolarity pol)
  where
    pol = getModalPolarity p

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Also allow the use of irrelevant definitions.
applyRelevanceToContext :: (MonadTCEnv tcm, LensRelevance r) => r -> tcm a -> tcm a
applyRelevanceToContext thing =
  applyUnless (isRelevant rel)
   $ applyRelevanceToContextOnly   rel
   . applyRelevanceToJudgementOnly rel
  where rel = getRelevance thing

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Precondition: @Relevance /= Relevant@
applyRelevanceToContextOnly :: (MonadTCEnv tcm) => Relevance -> tcm a -> tcm a
applyRelevanceToContextOnly rel = localTC
  $ over eContext     (map $ inverseApplyRelevance rel)
  . over eLetBindings (Map.map . fmap . onLetBindingType $ inverseApplyRelevance rel)

-- | Apply relevance @rel@ the the relevance annotation of the (typing/equality)
--   judgement.  This is part of the work done when going into a @rel@-context.
--
--   Precondition: @Relevance /= Relevant@
applyRelevanceToJudgementOnly :: (MonadTCEnv tcm) => Relevance -> tcm a -> tcm a
applyRelevanceToJudgementOnly = localTC . over eRelevance . composeRelevance

-- | Like 'applyRelevanceToContext', but only act on context if
--   @--irrelevant-projections@.
--   See issue #2170.
applyRelevanceToContextFunBody :: (MonadTCM tcm, LensRelevance r) => r -> tcm a -> tcm a
applyRelevanceToContextFunBody thing cont =
  case getRelevance thing of
    Relevant{} -> cont
    rel -> applyWhenM (optIrrelevantProjections <$> pragmaOptions)
      (applyRelevanceToContextOnly rel) $    -- enable local irr. defs only when option
      applyRelevanceToJudgementOnly rel cont -- enable global irr. defs alway

-- | Apply the quantity to the quantity annotation of the
-- (typing/equality) judgement.
--
-- Precondition: The quantity must not be @'Quantity1' something@.
applyQuantityToJudgement ::
  (MonadTCEnv tcm, LensQuantity q) => q -> tcm a -> tcm a
applyQuantityToJudgement =
  localTC . over eQuantity . composeQuantity . getQuantity

-- | Apply inverse composition with the given cohesion to the typing context.
applyCohesionToContext :: (MonadTCEnv tcm, LensCohesion m) => m -> tcm a -> tcm a
applyCohesionToContext thing =
  case getCohesion thing of
    m | m == unitCohesion -> id
      | otherwise         -> applyCohesionToContextOnly   m
                             -- Cohesion does not apply to the judgment.

applyCohesionToContextOnly :: (MonadTCEnv tcm) => Cohesion -> tcm a -> tcm a
applyCohesionToContextOnly q = localTC
  $ over eContext     (map $ inverseApplyCohesion q)
  . over eLetBindings (Map.map . fmap . onLetBindingType $ inverseApplyCohesion q)

-- | Can we split on arguments of the given cohesion?
splittableCohesion :: (HasOptions m, LensCohesion a) => a -> m Bool
splittableCohesion a = do
  let c = getCohesion a
  pure (usableCohesion c) `and2M` (pure (c /= Flat) `or2M` do optFlatSplit <$> pragmaOptions)


{-# SPECIALIZE applyModalityToContext :: Modality -> TCM a -> TCM a #-}
-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
--
--   Also allow the use of irrelevant definitions.
--
--   This function might also do something for other modalities.
applyModalityToContext :: (MonadTCEnv tcm, LensModality m) => m -> tcm a -> tcm a
applyModalityToContext thing =
  case getModality thing of
    m | m == unitModality -> id
      | otherwise         -> applyModalityToContextOnly   m
                           . applyModalityToJudgementOnly m

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the
--   argument.
--
--   This function might also do something for other modalities, but
--   not for quantities.
--
--   Precondition: @Modality /= Relevant@
applyModalityToContextOnly :: (MonadTCEnv tcm) => Modality -> tcm a -> tcm a
applyModalityToContextOnly m = localTC
  $ over eContext (map $ inverseApplyModalityButNotQuantity m)
  . over eLetBindings
      (Map.map . fmap . onLetBindingType $ inverseApplyModalityButNotQuantity m)

-- | Apply the relevance and quantity components of the modality to
-- the modality annotation of the (typing/equality) judgement.
--
-- Precondition: The relevance component must not be 'Relevant'.
applyModalityToJudgementOnly :: (MonadTCEnv tcm) => Modality -> tcm a -> tcm a
applyModalityToJudgementOnly m =
  localTC $ over eRelevance (composeRelevance (getRelevance m)) .
            over eQuantity  (composeQuantity  (getQuantity m))

-- | Like 'applyModalityToContext', but only act on context (for Relevance) if
--   @--irrelevant-projections@.
--   See issue #2170.
applyModalityToContextFunBody :: (MonadTCM tcm, LensModality r) => r -> tcm a -> tcm a
applyModalityToContextFunBody thing cont = do
    ifM (optIrrelevantProjections <$> pragmaOptions)
      {-then-} (applyModalityToContext m cont)                -- enable global irr. defs always
      {-else-} (applyRelevanceToContextFunBody (getRelevance m)
               $ applyCohesionToContext (getCohesion m)
               $ applyPolarityToContext (getModalPolarity m)
               $ applyQuantityToJudgement (getQuantity m) cont) -- enable local irr. defs only when option
  where
    m = getModality thing

-- | Wake up irrelevant variables and make them relevant. This is used
--   when type checking terms in a hole, in which case you want to be able to
--   (for instance) infer the type of an irrelevant variable. In the course
--   of type checking an irrelevant function argument 'applyRelevanceToContext'
--   is used instead, which also sets the context relevance to 'Irrelevant'.
--   This is not the right thing to do when type checking interactively in a
--   hole since it also marks all metas created during type checking as
--   irrelevant (issue #2568).
--
--   Also set the current quantity to 0.
wakeIrrelevantVars :: (MonadTCEnv tcm) => tcm a -> tcm a
wakeIrrelevantVars
  = applyRelevanceToContextOnly irrelevant
  . applyQuantityToJudgement zeroQuantity
