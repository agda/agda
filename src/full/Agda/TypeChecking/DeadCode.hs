{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.DeadCode (eliminateDeadCode) where

import Control.Monad (filterM)
import Control.Monad.Trans

import Data.Maybe
import qualified Data.Map.Strict as MapS
import qualified Data.HashMap.Strict as HMap

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base

import qualified Agda.Benchmarking as Bench
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad

import Agda.Utils.Monad (mapMaybeM)
import Agda.Utils.Impossible
import Agda.Utils.Lens

import Agda.Utils.HashTable (HashTable)
import qualified Agda.Utils.HashTable as HT

-- | Run before serialisation to remove data that's not reachable from the
--   public interface. We do not compute reachable data precisely, because that
--   would be very expensive, mainly because of rewrite rules. The following
--   things are assumed to be "roots":
--     - public definitions
--     - definitions marked as primitive
--     - definitions with COMPILE pragma
--     - all pattern synonyms (because currently all of them go into interfaces)
--     - all parameter sections (because currently all of them go into interfaces)
--       (see also issues #6931 and #7382)
--     - local builtins
--     - all rewrite rules
--     - closed display forms
--   We only ever prune dead metavariables and definitions. We return the pruned metas,
--   pruned definitions and closed display forms.
eliminateDeadCode :: ScopeInfo -> TCM (RemoteMetaStore, Definitions, DisplayForms)
eliminateDeadCode !scope = Bench.billTo [Bench.DeadCode] $ do
  !sig <- getSignature
  let !defs = sig ^. sigDefinitions
  !metas <- useR stSolvedMetaStore

  -- #2921: Eliminating definitions with attached COMPILE pragmas results in
  -- the pragmas not being checked. Simple solution: don't eliminate these.
  -- #6022 (Andreas, 2022-09-30): Eliminating cubical primitives can lead to crashes.
  -- Simple solution: retain all primitives (shouldn't be many).
  let hasCompilePragma = not . MapS.null . defCompiledRep

      isPrimitive = \case
        Primitive{}     -> True
        PrimitiveSort{} -> True
        _               -> False

      extraRootsFilter (name, def)
        | hasCompilePragma def || isPrimitive (theDef def) = Just name
        | otherwise = Nothing

  let !pubModules = publicModules scope

    -- Ulf, 2016-04-12:
    -- Non-closed display forms are not applicable outside the module anyway,
    -- and should be dead-code eliminated (#1928).
  !rootDisplayForms <-
      HMap.filter (not . null) . HMap.map (filter isClosed) <$> useTC stImportsDisplayForms

  let !rootPubNames  = map anameName $ publicNamesOfModules pubModules
  let !rootExtraDefs = mapMaybe extraRootsFilter $ HMap.toList defs
  let !rootRewrites  = sig ^. sigRewriteRules
  let !rootModSections = sig ^. sigSections
  !rootBuiltins <- useTC stLocalBuiltins
  !rootPatSyns  <- getPatternSyns

  !seenNames <- liftIO HT.empty :: TCM (HashTable QName ())
  !seenMetas <- liftIO HT.empty :: TCM (HashTable MetaId ())

  let goName :: QName -> IO ()
      goName !x = HT.lookup seenNames x >>= \case
        Just _ ->
          pure ()
        Nothing -> do
          HT.insert seenNames x ()
          go (HMap.lookup x defs)

      goMeta :: MetaId -> IO ()
      goMeta !m = HT.lookup seenMetas m >>= \case
        Just _ ->
          pure ()
        Nothing -> do
          HT.insert seenMetas m ()
          case MapS.lookup m metas of
            Nothing -> pure ()
            Just mv -> do
              go (instBody (theInstantiation mv))
              go (jMetaType (mvJudgement mv))

      go :: NamesIn a => a -> IO ()
      go !x = namesAndMetasIn' (either goName goMeta) x
      {-# INLINE go #-}

  Bench.billTo [Bench.DeadCode, Bench.DeadCodeReachable] $ liftIO $ do
    go rootDisplayForms
    foldMap goName rootPubNames
    foldMap goName rootExtraDefs
    go rootRewrites
    go rootModSections
    go rootBuiltins
    foldMap (go . PSyn) rootPatSyns

  let filterMeta :: (MetaId, MetaVariable) -> IO (Maybe (MetaId, RemoteMetaVariable))
      filterMeta (!i, !m) = HT.lookup seenMetas i >>= \case
        Nothing -> pure Nothing
        Just _  -> let !m' = remoteMetaVariable m in pure $ Just (i, m')

      filterDef :: (QName, Definition) -> IO Bool
      filterDef (!x, !d) = HT.lookup seenNames x >>= \case
        Nothing -> pure False
        Just _  -> pure True

  !metas <- liftIO $ HMap.fromList <$> mapMaybeM filterMeta (MapS.toList metas)
  !defs  <- liftIO $ HMap.fromList <$> filterM filterDef (HMap.toList defs)
  pure (metas, defs, rootDisplayForms)

-- | Returns the instantiation.
--   Precondition: The instantiation must be of the form @'InstV' inst@.
theInstantiation :: MetaVariable -> Instantiation
theInstantiation mv = case mvInstantiation mv of
  InstV inst                     -> inst
  OpenMeta{}                     -> __IMPOSSIBLE__
  BlockedConst{}                 -> __IMPOSSIBLE__
  PostponedTypeCheckingProblem{} -> __IMPOSSIBLE__

-- | Converts from 'MetaVariable' to 'RemoteMetaVariable'.
--   Precondition: The instantiation must be of the form @'InstV' inst@.
remoteMetaVariable :: MetaVariable -> RemoteMetaVariable
remoteMetaVariable !mv = RemoteMetaVariable
  { rmvInstantiation = theInstantiation mv
  , rmvModality      = getModality mv
  , rmvJudgement     = mvJudgement mv
  }
