{-# LANGUAGE BangPatterns #-}

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
  , withoutCache

    -- * Restoring the 'PostScopeState'
  , restorePostScopeState
  ) where


import qualified Data.Map as Map

import Agda.Syntax.Common

import Agda.Interaction.Options

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Debug
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options

import Agda.Utils.Lens
import Agda.Utils.Monad

import Agda.Utils.Impossible

-- | To be called before any write or restore calls.
cachingStarts :: TCM ()
cachingStarts = do
    NameId _ m <- useTC stFreshNameId
    stFreshNameId `setTCLens` NameId 1 m
    stAreWeCaching `setTCLens` True

areWeCaching :: (ReadTCState m) => m Bool
areWeCaching = useR stAreWeCaching

-- | Writes a 'TypeCheckAction' to the current log, using the current
-- 'PostScopeState'
writeToCurrentLog :: TypeCheckAction -> TCM ()
writeToCurrentLog !d = do
  reportSLn "cache" 10 $ "cachePostScopeState"
  !l <- getsTC stPostScopeState
  modifyCache $ fmap $ \lfc -> lfc{ lfcCurrent = (d, l) : lfcCurrent lfc}

restorePostScopeState :: PostScopeState -> TCM ()
restorePostScopeState pss = do
  reportSLn "cache" 10 $ "restorePostScopeState"
  modifyTC $ \s ->
    let ipoints = s^.stInteractionPoints
        ws = s^.stTCWarnings
        pss' = pss{stPostInteractionPoints = stPostInteractionPoints pss `mergeIPMap` ipoints
                  ,stPostTCWarnings = stPostTCWarnings pss `mergeWarnings` ws
                  }
    in  s{stPostScopeState = pss'}
  where
    mergeIPMap lm sm = Map.mapWithKey (\k v -> maybe v (`mergeIP` v) (Map.lookup k lm)) sm
    -- see #1338 on why we need to use the new ranges.
    mergeIP li si = li { ipRange = ipRange si }

    mergeWarnings loading current = [ w | w <- current, not $ tcWarningCached w ]
                                 ++ [ w | w <- loading,       tcWarningCached w ]

modifyCache
  :: (Maybe LoadedFileCache -> Maybe LoadedFileCache)
  -> TCM ()
modifyCache f = do
  modifyTC $ \s -> let !p = stPersistentState s in s
    { stPersistentState =
                          p { stLoadedFileCache = f (stLoadedFileCache p)}
    }

getCache :: TCM (Maybe LoadedFileCache)
getCache = do
  getsTC (stLoadedFileCache . stPersistentState)

putCache :: Maybe LoadedFileCache -> TCM ()
putCache cs = modifyCache $ const cs

-- | Runs the action without cache and restores the current cache at
-- the end of it.
withoutCache :: TCM a -> TCM a
withoutCache m =
  bracket_ getCache putCache $ do
    modifyCache (const Nothing)
    m

-- | Reads the next entry in the cached type check log, if present.
readFromCachedLog :: TCM (Maybe (TypeCheckAction, PostScopeState))
readFromCachedLog = do
  reportSLn "cache" 10 $ "getCachedTypeCheckAction"
  mbCache <- getCache
  case mbCache of
    Just lfc | (entry : entries) <- lfcCached lfc -> do
      putCache $ Just lfc{lfcCached = entries}
      return (Just entry)
    _ -> do
      return Nothing

-- | Empties the "to read" CachedState. To be used when it gets invalid.
cleanCachedLog :: TCM ()
cleanCachedLog = do
  reportSLn "cache" 10 $ "cleanCachedLog"
  modifyCache $ fmap $ \lfc -> lfc{lfcCached = []}

-- | Makes sure that the 'stLoadedFileCache' is 'Just', with a clean
-- current log. Crashes is 'stLoadedFileCache' is already active with a
-- dirty log.  Should be called when we start typechecking the current
-- file.
activateLoadedFileCache :: TCM ()
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
cacheCurrentLog :: TCM ()
cacheCurrentLog = do
  reportSLn "cache" 10 $ "cacheCurrentTypeCheckLog"
  modifyCache $ fmap $ \lfc ->
    lfc{lfcCached = reverse (lfcCurrent lfc), lfcCurrent = []}
