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

import Data.Map qualified as Map
import Data.List as List

import qualified Agda.Benchmarking as Bench
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Info (pattern UnificationMeta)
import Agda.Syntax.Internal
import Agda.Syntax.Position (Range, noRange)
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.InternalToAbstract (reify, blankNotInScope)
import Agda.Syntax.Concrete.Name as Name
import Agda.Syntax.Common.Pretty as CPretty
import Agda.TypeChecking.CheckInternal ( checkInternal )
import Agda.TypeChecking.Empty (isEmptyType)
import Agda.TypeChecking.Level (levelType)
import Agda.TypeChecking.MetaVars (newValueMeta)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty as TCPretty
import Agda.TypeChecking.Reduce (reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Rules.Term  (makeAbsurdLambda)
import Agda.TypeChecking.Substitute (apply)
import Agda.Utils.List1 qualified as List1

import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (normalForm, getModuleContents)

-- temporarily a tuple of name and type
type LemmingsResult = [(Name.Name, Type)]

-- entry point for running inside a hole
lemmings :: MonadTCM tcm
  => Rewrite
  -> InteractionId -- the hole to run onn
  -> Range
  -> String
  -> tcm LemmingsResult
lemmings norm iid rng str = liftTCM $ do
  reportSDoc "lemmings.top" 10 (TCPretty.text "Running Lemmings on interaction point" TCPretty.<+> TCPretty.pretty iid)

  -- first we just want to get everything in scope
  scope <- getInteractionScope iid
  (modules, context, names) <- getModuleContents norm Nothing

  -- get a list of scopes from ScopeInfo and then extract names
  let scopeMods = Map.toList $ scope ^. scopeModules
  let names = map (\(mod, scope) -> (nsNames . allThingsInScope) scope) scopeMods

  -- took filtering from SearchAbout
  let namesInScope = concat
                     $ map (\snms -> filter ((PatternSynName /=) . anameKind . snd)
                     $ List1.concat
                     $ map (\(c, as) -> fmap (c,) as)
                     $ Map.toList snms) names

  -- get normalised types of all names in scope
  res <- forM namesInScope $ \(x, n) -> do
    t <- normalForm norm =<< typeOfConst (anameName n)
    return (x, t)

  -- NOTE: try filtering by if the types are an instance of the goal type
  --       and perhaps combine this with the ideas given by Reed
  --
  --       instance should be more general than equalType
  --       need to look into one unification function needs to be called to check this
  --
  --       but of course, this may be incredibly slow
  --
  --       ideas for after this: figure out a good way of indexing by instace/unification

  reportSDoc "lemmings.top" 10 ((TCPretty.text "Found ") TCPretty.<+> (TCPretty.text (show $ length namesInScope)) TCPretty.<+> (TCPretty.text " names"))

  return res
