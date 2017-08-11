-- {-# LANGUAGE CPP #-}

{-| Irrelevant function types.
-}
module Agda.TypeChecking.Irrelevance where

import Control.Arrow (first, second)
import Control.Applicative
import Control.Monad.Reader

import qualified Data.Map as Map

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Monad

-- | data 'Relevance'
--   see "Agda.Syntax.Common".

-- * Operations on 'Dom'.

-- | Prepare parts of a parameter telescope for abstraction in constructors
--   and projections.
hideAndRelParams :: Dom a -> Dom a
hideAndRelParams = hideOrKeepInstance . mapRelevance nonStrictToIrr

-- | Used to modify context when going into a @rel@ argument.
inverseApplyRelevance :: Relevance -> Dom a -> Dom a
inverseApplyRelevance rel = mapRelevance (rel `inverseComposeRelevance`)

-- | Compose two relevance flags.
--   This function is used to update the relevance information
--   on pattern variables @a@ after a match against something @rel@.
applyRelevance :: Relevance -> Dom a -> Dom a
applyRelevance rel = mapRelevance (rel `composeRelevance`)

-- * Operations on 'Context'.

-- | Modify the context whenever going from the l.h.s. (term side)
--   of the typing judgement to the r.h.s. (type side).
workOnTypes :: TCM a -> TCM a
workOnTypes cont = do
  allowed <- optExperimentalIrrelevance <$> pragmaOptions
  verboseBracket "tc.irr" 20 "workOnTypes" $ workOnTypes' allowed cont

-- | Internal workhorse, expects value of --experimental-irrelevance flag
--   as argument.
workOnTypes' :: Bool -> TCM a -> TCM a
workOnTypes' experimental cont = modifyContext (modifyContextEntries $ mapRelevance f) cont
  where
    f | experimental = irrToNonStrict . nonStrictToRel
      | otherwise    = nonStrictToRel

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
applyRelevanceToContext :: Relevance -> TCM a -> TCM a
applyRelevanceToContext rel =
  case rel of
    Relevant -> id
    Forced{} -> id
    _        -> local $ \ e -> e
      { envContext     = modifyContextEntries      (inverseApplyRelevance rel) (envContext e)
      , envLetBindings = (Map.map . fmap . second) (inverseApplyRelevance rel) (envLetBindings e)
                                                  -- enable local  irr. defs
      , envRelevance   = composeRelevance rel (envRelevance e)
                                                  -- enable global irr. defs
      }

-- | Wake up irrelevant variables and make them relevant. This is used
--   when type checking terms in a hole, in which case you want to be able to
--   (for instance) infer the type of an irrelevant variable. In the course
--   of type checking an irrelevant function argument 'applyRelevanceToContext'
--   is used instead, which also sets the context relevance to 'Irrelevant'.
--   This is not the right thing to do when type checking interactively in a
--   hole since it also marks all metas created during type checking as
--   irrelevant (issue #2568).
wakeIrrelevantVars :: TCM a -> TCM a
wakeIrrelevantVars = local $ \ e -> e
  { envContext     = modifyContextEntries      (inverseApplyRelevance Irrelevant) (envContext e)
  , envLetBindings = (Map.map . fmap . second) (inverseApplyRelevance Irrelevant) (envLetBindings e)
  }

