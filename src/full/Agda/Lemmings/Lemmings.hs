-- | Lemmings is the backbone of a new search tool for Agda
--   and is currently under-development.
--
--  Once complete, Lemmings will allow the user to gain a list of viable
--  lemmas or proofs that could be applied in some form to the current goal
--  and/or search for proofs/functions/datatypes in a similar fashion to
--  Hoogle
module Agda.Lemmings.Lemmings where

-- for now, steal possibly relevant imports from Mimer
import Prelude hiding (null)

import Control.Monad

import qualified Agda.Benchmarking as Bench
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Info (pattern UnificationMeta)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range, noRange)
import Agda.Syntax.Translation.InternalToAbstract (reify, blankNotInScope)

import Agda.TypeChecking.CheckInternal ( checkInternal )
import Agda.TypeChecking.Empty (isEmptyType)
import Agda.TypeChecking.Level (levelType)
import Agda.TypeChecking.MetaVars (newValueMeta)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce (reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Rules.Term  (makeAbsurdLambda)
import Agda.TypeChecking.Substitute (apply)

import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (normalForm)

-- temporarily a String
type LemmingsResult = String

-- entry point for running inside a hole 
lemmingsHole :: MonadTCM tcm
  => InteractionId -- the hole to run onn
  -> tcm LemmingsResult
lemmingsHole iid = liftTCM $ do
  reportSDoc "lemmings.top" 10 (do
    (text "Running Lemmings on interaction point"))
    
  return "TODO: implement"
