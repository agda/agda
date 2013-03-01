{-# LANGUAGE CPP #-}

{-| Irrelevant function types.
-}
module Agda.TypeChecking.Irrelevance where

import Control.Applicative
import Control.Monad.Reader

import qualified Data.Map as Map

import Agda.Interaction.Options hiding (tests)

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg, ArgInfo)
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Internal (Arg, Dom, NamedArg, ArgInfo)

import Agda.TypeChecking.Monad

#include "../undefined.h"
import Agda.Utils.Impossible
import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers

-- | data 'Relevance'
--   see 'Agda.Syntax.Common'

irrelevantOrUnused :: Relevance -> Bool
irrelevantOrUnused Irrelevant = True
irrelevantOrUnused UnusedArg  = True
irrelevantOrUnused NonStrict  = False
irrelevantOrUnused Relevant   = False
irrelevantOrUnused Forced     = False

-- | @unusableRelevance rel == True@ iff we cannot use a variable of @rel@.
unusableRelevance :: Relevance -> Bool
unusableRelevance rel = NonStrict `moreRelevant` rel

-- | 'Relevance' composition.
--   'Irrelevant' is dominant, 'Relevant' is neutral.
composeRelevance :: Relevance -> Relevance -> Relevance
composeRelevance r r' =
  case (r, r') of
    (Irrelevant, _) -> Irrelevant
    (_, Irrelevant) -> Irrelevant
    (NonStrict, _)  -> NonStrict
    (_, NonStrict)  -> NonStrict
    (Forced, _)     -> Forced
    (_, Forced)     -> Forced
    (UnusedArg, _)  -> UnusedArg
    (_, UnusedArg)  -> UnusedArg
    (Relevant, Relevant) -> Relevant

-- | @inverseComposeRelevance r x@ returns the most irrelevant @y@
--   such that forall @x@, @y@ we have
--   @x \`moreRelevant\` (r \`composeRelevance\` y)@
--   iff
--   @(r \`inverseComposeRelevance\` x) \`moreRelevant\` y@ (Galois connection).
inverseComposeRelevance :: Relevance -> Relevance -> Relevance
inverseComposeRelevance r x =
  case (r, x) of
    (Relevant, x)        -> x          -- going to relevant arg.: nothing changes
    _ | r == x           -> Relevant   -- because Relevant is comp.-neutral
    (UnusedArg, x)       -> x
    (Forced, UnusedArg)  -> Relevant
    (Forced, x)          -> x
    (Irrelevant, x)      -> Relevant   -- going irrelevant: every thing usable
    (_, Irrelevant)      -> Irrelevant -- otherwise: irrelevant things remain unusable
    (NonStrict, _)       -> Relevant   -- but @NonStrict@s become usable

-- | For comparing @Relevance@ ignoring @Forced@ and @UnusedArg@.
ignoreForced :: Relevance -> Relevance
ignoreForced Forced     = Relevant
ignoreForced UnusedArg  = Relevant
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
hideAndRelParams = setHiding Hidden . mapRelevance nonStrictToIrr

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

-- | Call me if --experimental-irrelevance is set.
doWorkOnTypes :: TCM a -> TCM a
doWorkOnTypes = verboseBracket "tc.irr" 20 "workOnTypes" . workOnTypes' True

-- | Internal workhorse, expects value of --experimental-irrelevance flag
--   as argument.
workOnTypes' :: Bool -> TCM a -> TCM a
workOnTypes' allowed cont =
  if allowed then
    liftTCM $ modifyContext (modifyContextEntries $ mapRelevance $ irrToNonStrict) cont
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
      , envRelevance = composeRelevance rel (envRelevance e)
                                                  -- enable global irr. defs
      }

-- | Wake up irrelevant variables and make them relevant.  For instance,
--   in an irrelevant function argument otherwise irrelevant variables
--   may be used, so they are awoken before type checking the argument.
wakeIrrelevantVars :: TCM a -> TCM a
wakeIrrelevantVars = applyRelevanceToContext Irrelevant


------------------------------------------------------------------------
-- * Tests
------------------------------------------------------------------------

prop_galois :: Relevance -> Relevance -> Relevance -> Bool
prop_galois r x y =
  x `moreRelevant` (r `composeRelevance` y) ==
  (r `inverseComposeRelevance` x) `moreRelevant` y

tests :: IO Bool
tests = runTests "Agda.TypeChecking.Irrelevance"
  [ quickCheck' prop_galois
  ]
