{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.DeadCode (eliminateDeadCode) where

import Control.Monad ((<$!>))
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
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base

import qualified Agda.Benchmarking as Bench
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce

import Agda.Utils.Impossible
import Agda.Utils.Lens

import Agda.Utils.HashTable (HashTable)
import qualified Agda.Utils.HashTable as HT

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
  !patsyn <- getPatternSyns
  !public <- Set.mapMonotonic anameName . publicNames <$> getScope
  !save   <- optSaveMetas <$> pragmaOptions
  !defs   <- if save then return (sig ^. sigDefinitions)
                     else Bench.billTo [Bench.DeadCode, Bench.DeadCodeInstantiateFull]
                          (traverse (\x -> instantiateFull x) (sig ^. sigDefinitions))

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

  (!rns, !rms) <- Bench.billTo [Bench.DeadCode, Bench.DeadCodeReachable] $ liftIO $
                    reachableFrom (rootNames, rootMetas) patsyn disp defs ms

  let !dead  = Set.fromList (HMap.keys defs) `Set.difference` rns
      !valid = getAll . namesIn' (All . (`Set.notMember` dead))  -- no used name is dead
      !defs' = HMap.map ( \ d -> d { defDisplay = filter valid (defDisplay d) } )
               $ HMap.filterWithKey (\ x _ -> Set.member x rns) defs
      !disp' = HMap.filter (not . null) $ HMap.map (filter valid) disp
      !ms'   = HMap.fromList $
                mapMaybe
                  (\(m, mv) ->
                    if not (Set.member m rms)
                    then Nothing
                    else Just (m, remoteMetaVariable mv)) $
                MapS.toList ms

  reportSLn "tc.dead" 10 $
    "Removed " ++ show (HMap.size defs - HMap.size defs') ++
    " unused definitions and " ++ show (MapS.size ms - HMap.size ms') ++
    " unused meta-variables."
  reportSLn "tc.dead" 90 $ unlines $
    "Removed the following definitions from the signature:" :
    map (("- " ++) . prettyShow) (Set.toList dead)
  let !sig' = set sigDefinitions defs' sig
  return (disp', sig', ms')

reachableFrom
  :: (Set QName, Set MetaId)  -- ^ Roots.
  -> A.PatternSynDefns -> DisplayForms -> Definitions -> LocalMetaStore
  -> IO (Set QName, Set MetaId)
reachableFrom (ids, ms) psyns disp defs insts = do

  !seenNames <- HT.empty :: IO (HashTable QName ())
  !seenMetas <- HT.empty :: IO (HashTable MetaId ())

  let goName :: QName -> IO ()
      goName !x = HT.lookup seenNames x >>= \case
        Just _ ->
          pure ()
        Nothing -> do
          HT.insert seenNames x ()
          go (HMap.lookup x defs)
          go (PSyn <$!> MapS.lookup x psyns)
          go (HMap.lookup x disp)

      goMeta :: MetaId -> IO ()
      goMeta !m = HT.lookup seenMetas m >>= \case
        Just _ ->
          pure ()
        Nothing -> do
          HT.insert seenMetas m ()
          case MapS.lookup m insts of
            Nothing -> pure ()
            Just mv -> go (instBody (theInstantiation mv))

      go :: NamesIn a => a -> IO ()
      go = namesAndMetasIn' (either goName goMeta)
      {-# INLINE go #-}

  foldMap goName ids
  foldMap goMeta ms
  !ids' <- HT.keySet seenNames
  !ms'  <- HT.keySet seenMetas
  pure (ids', ms')


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
