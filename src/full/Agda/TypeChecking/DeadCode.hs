{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.DeadCode (eliminateDeadCode) where

import Control.Monad
import Control.Monad.Trans

import Data.Maybe
import qualified Data.Map.Strict as MapS
import qualified Data.HashMap.Strict as HMap
import Data.IORef

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Scope.Base

import qualified Agda.Benchmarking as Bench
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TypeChecking.Monad

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List
import qualified Agda.Utils.List1 as List1

import Agda.Utils.HashTable (HashTableLU, HashTableLL)
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
          -- Andreas, 2025-11-18, issue #8037
          -- When copying the record type along with one of its projections in a module application,
          -- we need to make sure the record type has not been deleted as deadcode.
        | Just Projection{ projProper = Just r } <- isProjection_ (theDef def) = Just r
        | otherwise = Nothing

  let !pubModules = publicModules scope

    -- Ulf, 2016-04-12:
    -- Non-closed display forms are not applicable outside the module anyway,
    -- and should be dead-code eliminated (#1928).
  let eliminateNonClosed = List1.nonEmpty . List1.filter isClosed

  !rootDisplayForms <-
      HMap.mapMaybe eliminateNonClosed <$> useTC stImportsDisplayForms

  let !rootPubNames  = map' anameName $ publicNamesOfModules pubModules
  let !rootExtraDefs = mapMaybe extraRootsFilter $ HMap.toList defs
  let !rootRewrites  = sig ^. sigRewriteRules
  let !rootModSections = sig ^. sigSections
  !rootBuiltins <- useTC stLocalBuiltins
  !rootPatSyns  <- getPatternSyns

  -- When we're traversing the definition of a name, we want to record if the definition contains
  -- any metas. If a definition doesn't contain metas, we can skip instantiateFull on it before
  -- serialization.
  --
  -- We record "meta-closedness" in the following way. If we're traversing a name definition,
  -- "insideDef" contains the IORef Bool which can be flipped if we hit a metavariable. We
  -- store these IORef Bool-s in "seenNames". A new IORef Bool is created for each QName when we
  -- encounter it for the first time.
  !insideDef <- lift $ newIORef Nothing :: TCM (IORef (Maybe (IORef Bool)))

  !seenNames <- lift $ HT.empty :: TCM (HashTableLL QName (IORef Bool))
  !seenMetas <- lift $ HT.empty :: TCM (HashTableLU MetaId ())

  let goName :: QName -> IO ()
      goName !x = HT.insertingIfAbsent seenNames x
        -- already visited name, do nothing
        (\_ -> pure ())

        -- unvisited, insert new IORef into table
        (newIORef False)

        (\ref -> do
            prevRef <- readIORef insideDef  -- save ref
            writeIORef insideDef (Just ref)
            go (HMap.lookup x defs)
            writeIORef insideDef prevRef    -- restore ref
        )

      goMeta :: MetaId -> IO ()
      goMeta !m = do
        prevRef <- readIORef insideDef
        case prevRef of
          -- we're not inside any name definition
          Nothing  -> pure ()
          -- we're inside a name definition, record meta occurrence
          Just ref -> writeIORef ref True

        HT.insertingIfAbsent seenMetas m
          -- already visited, do nothing
          (\_ -> pure ())

          (pure ())
          -- unvisited
          (\_ -> case MapS.lookup m metas of
            Nothing -> pure ()
            Just mv -> do
              writeIORef insideDef Nothing
              go (instBody (theInstantiation mv))
              go (jMetaType (mvJudgement mv))
              writeIORef insideDef prevRef -- restore ref
          )

      go :: NamesIn a => a -> IO ()
      go !x = namesAndMetasIn' (either goName goMeta) x
      {-# INLINE go #-}

  Bench.billTo [Bench.DeadCode, Bench.DeadCodeReachable] $ lift $ do
    go rootDisplayForms
    foldMap goName rootPubNames
    foldMap goName rootExtraDefs
    go rootRewrites
    go rootModSections
    go rootBuiltins
    foldMap go rootPatSyns

  let goMetas :: [(MetaId, MetaVariable)] -> IO [(MetaId, RemoteMetaVariable)]
      goMetas [] = pure []
      goMetas ((!i, !m):metas) = HT.lookup seenMetas i >>= \case
        Nothing -> goMetas metas
        Just _  -> do
          let !m' = remoteMetaVariable m
          ((i, m'):) <$!> goMetas metas

      goDefs :: [(QName, Definition)] -> IO [(QName, Definition)]
      goDefs [] = pure []
      goDefs ((!x, !d):defs) = HT.lookup seenNames x >>= \case
        Nothing -> goDefs defs
        Just r  -> do
          hasM <- readIORef r
          !d <- case hasM of
            True  -> pure d
            False -> pure $! d {defMightContainMetas = False}
          ((x, d):) <$!> goDefs defs

  !metas <- lift $ HMap.fromList <$> goMetas (MapS.toList metas)
  !defs  <- lift $ HMap.fromList <$> goDefs (HMap.toList defs)
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
