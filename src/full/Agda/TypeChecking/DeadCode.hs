module Agda.TypeChecking.DeadCode (eliminateDeadCode) where

import qualified Control.Exception as E
import Control.Monad.Trans

import Data.Maybe
import Data.Monoid (All(..))
import qualified Data.Map.Strict as MapS
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as HMap

import Agda.Interaction.Options

import qualified Agda.Syntax.Abstract as A

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base

import qualified Agda.Benchmarking as Bench
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.WithDefault

-- | Run before serialisation to remove any definitions and
-- meta-variables that are not reachable from the module's public
-- interface.
--
-- Things that are reachable only from warnings are removed.

eliminateDeadCode ::
  BuiltinThings PrimFun -> DisplayForms -> Signature ->
  LocalMetaStore ->
  TCM (DisplayForms, Signature, RemoteMetaStore)
eliminateDeadCode bs disp sig ms = Bench.billTo [Bench.DeadCode] $ do
  patsyn <- getPatternSyns
  public <- Set.mapMonotonic anameName . publicNames <$> getScope
  save   <- optSaveMetas <$> pragmaOptions
  defs   <- (if save then return else traverse instantiateFull)
                 (sig ^. sigDefinitions)
  -- #2921: Eliminating definitions with attached COMPILE pragmas results in
  -- the pragmas not being checked. Simple solution: don't eliminate these.
  -- #6022 (Andreas, 2022-09-30): Eliminating cubical primitives can lead to crashes.
   -- Simple solution: retain all primitives (shouldn't be many).
  let hasCompilePragma = not . MapS.null . defCompiledRep
      isPrimitive = \case
        Primitive{}     -> True
        PrimitiveSort{} -> True
        _ -> False
      extraRootsFilter (name, def)
        | hasCompilePragma def || isPrimitive (theDef def) = Just name
        | otherwise = Nothing
      extraRoots =
        Set.fromList $ mapMaybe extraRootsFilter $ HMap.toList defs

      rootNames = Set.union public extraRoots
      rootMetas =
        if not save then Set.empty else metasIn
          ( bs
          , sig ^. sigSections
          , sig ^. sigRewriteRules
          , HMap.filterWithKey (\x _ -> Set.member x rootNames) disp
          )
      (rns, rms) =
        reachableFrom (rootNames, rootMetas) patsyn disp defs ms
      dead  = Set.fromList (HMap.keys defs) `Set.difference` rns
      valid = getAll . namesIn' (All . (`Set.notMember` dead))  -- no used name is dead
      defs' = HMap.map ( \ d -> d { defDisplay = filter valid (defDisplay d) } )
            $ HMap.filterWithKey (\ x _ -> Set.member x rns) defs
      disp' = HMap.filter (not . null) $ HMap.map (filter valid) disp
      ms'   = HMap.fromList $
              mapMaybe
                (\(m, mv) ->
                  if not (Set.member m rms)
                  then Nothing
                  else Just (m, remoteMetaVariable mv)) $
              MapS.toList ms
  -- The hashmaps are forced to WHNF to ensure that the computations
  -- are billed to the right account.
  disp' <- liftIO $ E.evaluate disp'
  defs' <- liftIO $ E.evaluate defs'
  ms'   <- liftIO $ E.evaluate ms'
  reportSLn "tc.dead" 10 $
    "Removed " ++ show (HMap.size defs - HMap.size defs') ++
    " unused definitions and " ++ show (MapS.size ms - HMap.size ms') ++
    " unused meta-variables."
  return (disp', set sigDefinitions defs' sig, ms')

reachableFrom
  :: (Set QName, Set MetaId)  -- ^ Roots.
  -> A.PatternSynDefns -> DisplayForms -> Definitions -> LocalMetaStore
  -> (Set QName, Set MetaId)
reachableFrom (ids, ms) psyns disp defs insts =
  follow (ids, ms)
    (map Left (Set.toList ids) ++ map Right (Set.toList ms))
  where
  follow seen        []       = seen
  follow (!ids, !ms) (x : xs) =
    follow (Set.union ids'' ids, Set.union ms'' ms)
      (map Left  (Set.toList ids'') ++
       map Right (Set.toList ms'')  ++
       xs)
    where
    ids'' = ids' `Set.difference` ids
    ms''  = ms'  `Set.difference` ms

    (ids', ms') = case x of
      Left x ->
        namesAndMetasIn
          ( HMap.lookup x defs
          , PSyn <$> MapS.lookup x psyns
          , HMap.lookup x disp
          )
      Right m -> case MapS.lookup m insts of
        Nothing -> (Set.empty, Set.empty)
        Just mv -> namesAndMetasIn (instBody (theInstantiation mv))

-- | Returns the instantiation.
--
-- Precondition: The instantiation must be of the form @'InstV' inst@.

theInstantiation :: MetaVariable -> Instantiation
theInstantiation mv = case mvInstantiation mv of
  InstV inst                     -> inst
  Open{}                         -> __IMPOSSIBLE__
  OpenInstance{}                 -> __IMPOSSIBLE__
  BlockedConst{}                 -> __IMPOSSIBLE__
  PostponedTypeCheckingProblem{} -> __IMPOSSIBLE__

-- | Converts from 'MetaVariable' to 'RemoteMetaVariable'.
--
-- Precondition: The instantiation must be of the form @'InstV' inst@.

remoteMetaVariable :: MetaVariable -> RemoteMetaVariable
remoteMetaVariable mv = RemoteMetaVariable
  { rmvInstantiation = theInstantiation mv
  , rmvModality      = getModality mv
  , rmvJudgement     = mvJudgement mv
  }
