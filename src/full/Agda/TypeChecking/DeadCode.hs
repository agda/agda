module Agda.TypeChecking.DeadCode (eliminateDeadCode) where

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable (foldMap, Foldable)
import Data.Traversable (traverse)

import Agda.Syntax.Common
import Agda.Syntax.Literal
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Abstract as A

import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad

import qualified Agda.Benchmarking as Bench
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Reduce

import Agda.Utils.HashMap (HashMap)
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Lens

import Agda.Utils.Impossible

-- | Run before serialisation to remove any definitions that are not reachable
--   from the public interface to the module.
eliminateDeadCode :: DisplayForms -> Signature -> TCM (DisplayForms, Signature)
eliminateDeadCode disp sig = Bench.billTo [Bench.DeadCode] $ do
  patsyn <- getPatternSyns
  public <- Set.map anameName . publicNames <$> getScope
  defs <- traverse instantiateFull $ sig ^. sigDefinitions
  -- #2921: Eliminating definitions with attached COMPILE pragmas results in
  -- the pragmas not being checked. Simple solution: don't eliminate these.
  let hasCompilePragma = Set.fromList . HMap.keys . HMap.filter (not . Map.null . defCompiledRep) $ defs
  let r     = reachableFrom (Set.union public hasCompilePragma) patsyn defs
      dead  = Set.fromList (HMap.keys defs) `Set.difference` r
      valid = Set.null . Set.intersection dead . namesIn
      defs' = HMap.map ( \ d -> d { defDisplay = filter valid (defDisplay d) } )
            $ HMap.filterWithKey (\ x _ -> Set.member x r) defs
      disp' = HMap.filter (not . null) $ HMap.map (filter valid) disp
  reportSLn "tc.dead" 10 $ "Removed " ++ show (HMap.size defs - HMap.size defs') ++ " unused definitions."
  return (disp', set sigDefinitions defs' sig)

reachableFrom :: Set QName -> A.PatternSynDefns -> Definitions -> Set QName
reachableFrom names psyns defs = follow names (Set.toList names)
  where
    follow visited [] = visited
    follow visited (x : xs) = follow (Set.union visited new) (Set.toList new ++ xs)
      where
        new = Set.filter (not . (`Set.member` visited)) $
                case HMap.lookup x defs of
                  Nothing -> namesIn (PSyn <$> Map.lookup x psyns)
                  Just d  -> namesIn d

