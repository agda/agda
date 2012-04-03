{-# LANGUAGE CPP #-}

{-| Irrelevant function types.
-}
module Agda.TypeChecking.Irrelevance where

import Control.Applicative
import Control.Monad.Reader

import qualified Data.Map as Map

import Agda.Interaction.Options

import Agda.Syntax.Common

import Agda.TypeChecking.Monad

#include "../undefined.h"
import Agda.Utils.Impossible

-- | data 'Relevance'
--   see 'Agda.Syntax.Common'

-- | @unusableRelevance rel == True@ iff we cannot use a variable of @rel@.
unusableRelevance :: Relevance -> Bool
unusableRelevance rel = NonStrict `moreRelevant` rel

composeRelevance :: Relevance -> Relevance -> Relevance
composeRelevance r r' =
  case (r, r') of
    (Irrelevant, _) -> Irrelevant
    (_, Irrelevant) -> Irrelevant
    (NonStrict, _)  -> NonStrict
    (_, NonStrict)  -> NonStrict
    (Forced, _)     -> Forced
    (_, Forced)     -> Forced
    (Relevant, Relevant) -> Relevant

-- | @inverseComposeRelevance r x@ returns the most irrelevant @y@
--   such that forall @x@, @y@ we have
--   @x `moreRelevant` (r `composeRelevance` y)@
--   iff
--   @(r `inverseComposeRelevance` x) `moreRelevant` y@ (Galois connection).
inverseComposeRelevance :: Relevance -> Relevance -> Relevance
inverseComposeRelevance r x =
  case (r, x) of
    (_, Forced)          -> Forced     -- preserve @Forced@
    (Relevant, x)        -> x          -- going to relevant arg.: nothing changes
    (Forced, Relevant)   -> Forced     -- going forced: relevants become forced
    (Forced, x)          -> x
    (Irrelevant, _)      -> Relevant   -- going irrelevant: every thing usable
    (_, Irrelevant)      -> Irrelevant -- otherwise: irrelevant things remain unusable
    (NonStrict, _)       -> Relevant   -- but @NonStrict@s become usable

-- | For comparing @Relevance@ ignoring @Forced@.
ignoreForced :: Relevance -> Relevance
ignoreForced Forced     = Relevant
ignoreForced Relevant   = Relevant
ignoreForced NonStrict  = NonStrict
ignoreForced Irrelevant = Irrelevant

-- | Irrelevant function arguments may appear non-strictly in the codomain type.
irrToNonStrict :: Relevance -> Relevance
irrToNonStrict Irrelevant = NonStrict
-- irrToNonStrict NonStrict  = Relevant -- TODO: is that what we want (OR: NonStrict)  -- better be more conservative
irrToNonStrict rel        = rel

nonStrictToIrr :: Relevance -> Relevance
nonStrictToIrr NonStrict = Irrelevant
nonStrictToIrr rel       = rel

-- * Operations on 'Dom'.

-- | Prepare parts of a parameter telescope for abstraction in constructors
--   and projections.
hideAndRelParams :: Dom a -> Dom a
hideAndRelParams a = a
  { domRelevance = nonStrictToIrr (domRelevance a)
  , domHiding    = Hidden
  }

{- UNUSED
-- | @modifyArgRelevance f arg@ applies @f@ to the 'argRelevance' component of @arg@.
modifyArgRelevance :: (Relevance -> Relevance) -> Arg a -> Arg a
modifyArgRelevance f a = a { argRelevance = f (argRelevance a) }
-}

-- | Used to modify context when going into a @rel@ argument.
inverseApplyRelevance :: Relevance -> Dom a -> Dom a
inverseApplyRelevance rel = mapDomRelevance (rel `inverseComposeRelevance`)

-- | Compose two relevance flags.
--   This function is used to update the relevance information
--   on pattern variables @a@ after a match against something @rel@.
applyRelevance :: Relevance -> Dom a -> Dom a
applyRelevance rel = mapDomRelevance (rel `composeRelevance`)

-- * Operations on 'Context'.

-- | Modify the context whenever going from the l.h.s. (term side)
--   of the typing judgement to the r.h.s. (type side).
workOnTypes :: TCM a -> TCM a
workOnTypes cont = do
  allowed <- optExperimentalIrrelevance <$> pragmaOptions
  verboseBracket "tc.irr" 20 "workOnTypes" $ workOnTypes' allowed cont

-- | Call me if --experimental-irrelevance is set.
doWorkOnTypes :: TCM a -> TCM a
doWorkOnTypes = verboseBracket "tc.irr" 20 "workOnTypes" . workOnTypes' True

-- | Internal workhorse, expects value of --experimental-irrelevance flag
--   as argument.
workOnTypes' :: Bool -> TCM a -> TCM a
workOnTypes' allowed cont =
  if allowed then
    liftTCM $ modifyContext (modifyContextEntries $ mapDomRelevance $ irrToNonStrict) cont
   else cont

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
applyRelevanceToContext :: Relevance -> TCM a -> TCM a
applyRelevanceToContext rel =
  case rel of
    Relevant -> id
    Forced   -> id
    _        -> local $ \ e -> e
      { envContext   = modifyContextEntries (inverseApplyRelevance rel) (envContext e)
      , envLetBindings = Map.map
          (fmap $ \ (t, a) -> (t, inverseApplyRelevance rel a))
          (envLetBindings e)
                                                  -- enable local  irr. defs
      , envRelevance = rel                        -- enable global irr. defs
      }

-- | Wake up irrelevant variables and make them relevant.  For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
wakeIrrelevantVars :: TCM a -> TCM a
wakeIrrelevantVars = applyRelevanceToContext Irrelevant
