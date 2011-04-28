{-# LANGUAGE CPP #-}

{-| Irrelevant function types.
-}
module Agda.TypeChecking.Irrelevance where

import Control.Monad.Reader

import Agda.Syntax.Common

import Agda.TypeChecking.Monad
{-
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Context
-}

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

-- * Operations on 'Arg'.

-- | Prepare parts of a parameter telescope for abstraction in constructors
--   and projections.
hideAndRelParams :: Arg a -> Arg a
hideAndRelParams a = a
  { argRelevance = nonStrictToIrr (argRelevance a)
  , argHiding    = Hidden
  }

-- | @modifyArgRelevance f arg@ applies @f@ to the 'argRelevance' component of @arg@.
modifyArgRelevance :: (Relevance -> Relevance) -> Arg a -> Arg a
modifyArgRelevance f a = a { argRelevance = f (argRelevance a) }

-- | Used to modify context when going into a @rel@ argument.
inverseApplyRelevance :: Relevance -> Arg a -> Arg a
inverseApplyRelevance rel = modifyArgRelevance (rel `inverseComposeRelevance`)
-- inverseApplyRelevance rel a = a { argRelevance = rel `inverseComposeRelevance` argRelevance a }

-- | Compose two relevance flags.
--   This function is used to update the relevance information
--   on pattern variables @a@ after a match against something @rel@.
applyRelevance :: Relevance -> Arg a -> Arg a
applyRelevance rel = modifyArgRelevance (rel `composeRelevance`)
-- applyRelevance rel a = a { argRelevance = rel `composeRelevance` argRelevance a }

{- Andreas, 2011-04-26: the combination Irrelevant Forced does not arise
applyRelevance Irrelevant a | argRelevance a == Relevant =
  a { argRelevance = Irrelevant }
applyRelevance Forced a | argRelevance a == Relevant =
  a { argRelevance = Forced }
applyRelevance rel a = a -- ^ do nothing if rel == Relevant or a is
                         -- already Forced or Irrelevant
-}

-- * Operations on 'Context'.

-- | Modify the context whenever going from the l.h.s. (term side)
--   of the typing judgement to the r.h.s. (type side).
workOnTypes :: MonadTCM tcm => tcm a -> tcm a
workOnTypes = verboseBracket "tc.irr" 20 "workOnTypes" . workOnTypes'

workOnTypes' :: MonadTCM tcm => tcm a -> tcm a
workOnTypes' = modifyContext $ modifyContextEntries $ modifyArgRelevance $ irrToNonStrict

-- | (Conditionally) wake up irrelevant variables and make them relevant.
--   For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
applyRelevanceToContext :: MonadTCM tcm => Relevance -> tcm a -> tcm a
applyRelevanceToContext rel =
  case rel of
    Relevant -> id
    Forced   -> id
    _        -> local $ \ e -> e
      { envContext   = modifyContextEntries (inverseApplyRelevance rel) (envContext e)
                                                  -- enable local  irr. defs
      , envRelevance = rel                        -- enable global irr. defs
      }

{-
-- | Wake up irrelevant variables and make them relevant.  For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
wakeIrrelevantVars :: MonadTCM tcm => tcm a -> tcm a
wakeIrrelevantVars = local $ \ e -> e
   { envContext = map wakeVar (envContext e) -- enable local  irr. defs
   , envIrrelevant = True                    -- enable global irr. defs
   }
  where wakeVar ce = ce { ctxEntry = makeRelevant (ctxEntry ce) }

applyRelevanceToContext :: MonadTCM tcm => Relevance -> tcm a -> tcm a
applyRelevanceToContext Irrelevant cont = wakeIrrelevantVars cont
applyRelevanceToContext _          cont = cont
-}
