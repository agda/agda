{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Caching
  ( -- * Log reading/writing operations
    writeToCurrentLog
  , readFromCachedLog
  , cleanCachedLog
  , cacheCurrentLog

    -- * Activating/deactivating
  , activateLoadedFileCache
  , cachingStarts
  , areWeCaching
  , localCache, withoutCache

    -- * Restoring the 'PostScopeState'
  , restorePostScopeState
  ) where

import Agda.Syntax.Common

import Agda.Interaction.Options

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Null (empty)

import Agda.Utils.Impossible

-- | To be called before any write or restore calls.
{-# SPECIALIZE cachingStarts :: TCM () #-}
cachingStarts :: (MonadDebug m, MonadTCState m, ReadTCState m) => m ()
cachingStarts = do
    NameId _ m <- useTC stFreshNameId
    stFreshNameId `setTCLens` NameId 1 m
    stFreshOpaqueId `setTCLens` OpaqueId 1 m
    stAreWeCaching `setTCLens` True
    validateCache m -- fixes issue #4835
    where
      validateCache m = (localCache readFromCachedLog) >>= \case
        Just (_ , s) -> do
          let
            NameId _ m' = stPostFreshNameId s
            OpaqueId _ m'' = stPostFreshOpaqueId s
            stale = or [ m' /= m, m'' /= m ]
          when stale cleanCachedLog
        _ -> return ()

areWeCaching :: (ReadTCState m) => m Bool
areWeCaching = useR stAreWeCaching

-- | Writes a 'TypeCheckAction' to the current log, using the current
-- 'PostScopeState'
{-# SPECIALIZE writeToCurrentLog :: TypeCheckAction -> TCM () #-}
writeToCurrentLog :: (MonadDebug m, MonadTCState m, ReadTCState m) => TypeCheckAction -> m ()
writeToCurrentLog !d = do
  reportSLn "cache" 10 $ "cachePostScopeState"
  !l <- getsTC stPostScopeState
  modifyCache $ fmap $ \lfc -> lfc{ lfcCurrent = (d, l) : lfcCurrent lfc}

{-# SPECIALIZE restorePostScopeState :: PostScopeState -> TCM () #-}
restorePostScopeState :: (MonadDebug m, MonadTCState m) => PostScopeState -> m ()
restorePostScopeState pss = do
  reportSLn "cache" 10 $ "restorePostScopeState"
  modifyTC $ \s ->
    let ipoints = s^.stInteractionPoints
        ws = s^.stTCWarnings
        pss' = pss{stPostInteractionPoints = stPostInteractionPoints pss `mergeIPMap` ipoints
                  ,stPostTCWarnings = stPostTCWarnings pss `mergeWarnings` ws
                  ,stPostOpaqueBlocks = s ^. stOpaqueBlocks
                  ,stPostOpaqueIds = s ^. stOpaqueIds
                  }
    in  s{stPostScopeState = pss'}
  where
    mergeIPMap lm sm = BiMap.mapWithKey (\k v -> maybe v (`mergeIP` v) (BiMap.lookup k lm)) sm
    -- see #1338 on why we need to use the new ranges.
    mergeIP li si = li { ipRange = ipRange si }

    mergeWarnings loading current = [ w | w <- current, not $ tcWarningCached w ]
                                 ++ [ w | w <- loading,       tcWarningCached w ]

{-# SPECIALIZE modifyCache :: (Maybe LoadedFileCache -> Maybe LoadedFileCache) -> TCM () #-}
modifyCache
  :: MonadTCState m
  => (Maybe LoadedFileCache -> Maybe LoadedFileCache)
  -> m ()
modifyCache = modifyTCLens stLoadedFileCache

{-# SPECIALIZE getCache :: TCM (Maybe LoadedFileCache) #-}
getCache :: ReadTCState m => m (Maybe LoadedFileCache)
getCache = useTC stLoadedFileCache

{-# SPECIALIZE putCache :: Maybe LoadedFileCache -> TCM () #-}
putCache :: MonadTCState m => Maybe LoadedFileCache -> m ()
putCache = setTCLens stLoadedFileCache

-- | Runs the action and restores the current cache at the end of it.
{-# SPECIALIZE localCache :: TCM a -> TCM a #-}
localCache :: (MonadTCState m, ReadTCState m) => m a -> m a
localCache = bracket_ getCache putCache

-- | Runs the action without cache and restores the current cache at
-- the end of it.
{-# SPECIALIZE withoutCache :: TCM a -> TCM a #-}
withoutCache :: (MonadTCState m, ReadTCState m) => m a -> m a
withoutCache m = localCache $ do
    putCache empty
    m

-- | Reads the next entry in the cached type check log, if present.
{-# SPECIALIZE readFromCachedLog :: TCM (Maybe (TypeCheckAction, PostScopeState)) #-}
readFromCachedLog :: (MonadDebug m, MonadTCState m, ReadTCState m) => m (Maybe (TypeCheckAction, PostScopeState))
readFromCachedLog = do
  reportSLn "cache" 10 $ "getCachedTypeCheckAction"
  getCache >>= \case
    Just lfc | (entry : entries) <- lfcCached lfc -> do
      putCache $ Just lfc{lfcCached = entries}
      return (Just entry)
    _ -> do
      return Nothing

-- | Empties the "to read" CachedState. To be used when it gets invalid.
{-# SPECIALIZE cleanCachedLog :: TCM () #-}
cleanCachedLog :: (MonadDebug m, MonadTCState m) => m ()
cleanCachedLog = do
  reportSLn "cache" 10 $ "cleanCachedLog"
  modifyCache $ fmap $ \lfc -> lfc{lfcCached = []}

-- | Makes sure that the 'stLoadedFileCache' is 'Just', with a clean
-- current log. Crashes is 'stLoadedFileCache' is already active with a
-- dirty log.  Should be called when we start typechecking the current
-- file.
{-# SPECIALIZE activateLoadedFileCache :: TCM () #-}
activateLoadedFileCache :: (HasOptions m, MonadDebug m, MonadTCState m) => m ()
activateLoadedFileCache = do
  reportSLn "cache" 10 $ "activateLoadedFileCache"

  whenM (optGHCiInteraction <$> commandLineOptions) $
    whenM enableCaching $ do
      modifyCache $ \case
         Nothing                          -> Just $ LoadedFileCache [] []
         Just lfc | null (lfcCurrent lfc) -> Just lfc
         _                                -> __IMPOSSIBLE__

-- | Caches the current type check log.  Discardes the old cache.  Does
-- nothing if caching is inactive.
{-# SPECIALIZE cacheCurrentLog :: TCM () #-}
cacheCurrentLog :: (MonadDebug m, MonadTCState m) => m ()
cacheCurrentLog = do
  reportSLn "cache" 10 $ "cacheCurrentTypeCheckLog"
  modifyCache $ fmap $ \lfc ->
    lfc{lfcCached = reverse (lfcCurrent lfc), lfcCurrent = []}
