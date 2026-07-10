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

  let scopeMods = Map.toList $ scope ^. scopeModules
  let names = map (\(mod, scope) -> (nsNames . allThingsInScope) scope) scopeMods

  -- took filtering from SearchAbout
  -- TODO: cleanup
  let namesInScope = concat $ map (\snms -> filter ((PatternSynName /=) . anameKind . snd) $ List1.concat $ map (\(c, as) -> fmap (c,) as) $ Map.toList snms) names
         
  -- also yanked from SearchAbout but removed filtering
  res <- forM namesInScope $ \(x, n) -> do
    t <- normalForm norm =<< typeOfConst (anameName n)
    return (x, t)
    
  reportSDoc "lemmings.top" 10 ((TCPretty.text "Found ") TCPretty.<+> (TCPretty.text (show $ length namesInScope)) TCPretty.<+> (TCPretty.text " names"))
  
  return res

getAllNames :: Rewrite -> InteractionId -> Range -> String -> [Name.Name] -> TCM [(Name.Name, Type)]
getAllNames _ _ _ _ [] = return []
getAllNames norm iid rng str (m:ms) = do
  (modules, context, names) <- getModuleContents norm (Just (Name.QName m))
  rest <- getAllNames norm iid rng str ms
  return (names ++ rest)
  
-- so incredibly inneficient, just for testing
resultShow :: LemmingsResult -> CPretty.Doc
resultShow [] = ""
resultShow ((name, t):xs) = (CPretty.pretty name) CPretty.<+> (CPretty.text "\n")
resultShowName :: Name.Name -> String
resultShowName (Name.Name _ _ parts) = show parts
resultShowName (NoName _ _ ) = "no name given"
