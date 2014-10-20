module Agda.TypeChecking.Monad.Caching where

import Control.Arrow ((***), first, second)
import Control.Applicative
import qualified Control.Exception as E
import Control.Monad.State
import Data.Set (Set)
import Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Options


-- | Extracts the current loaded file state.
getFileState :: TCState -> LFileState
getFileState s = s { stPersistent = initPersistentState }

updateFileState :: LFileState -> TCState -> TCState
updateFileState l s = l
  {
    stPersistent = stPersistent s
  , stFreshThings = (stFreshThings l) { fInteraction = fInteraction (stFreshThings s)}
  , stInteractionPoints = stInteractionPoints l `mergeIP` stInteractionPoints s
  , stTokens = stTokens s
  , stImports = stImports s
  , stScope = stScope s
  }
  where
    mergeIP lm sm = Map.mapWithKey (\k v -> fromMaybe v (Map.lookup k lm)) sm

-- | Caches the current loaded file state.
-- The argument is supposed to be what was just typechecked.
cacheLFS :: CachedDecl-> TCM ()
cacheLFS d = do
  reportSLn "cache" 10 $ "cacheLFS"
  l <- gets getFileState
  l `seq` modifyCachedState $ fmap (second (++ [(d,l)]))

restoreLFS :: LFileState -> TCM ()
restoreLFS l = do
  reportSLn "cache" 10 $ "restoreLFS"
  modify $ updateFileState l

modifyCachedState :: (Maybe (CachedState,CachedState) -> Maybe (CachedState,CachedState)) -> TCM ()
modifyCachedState f = do
  modify $ \s -> s
    { stPersistent = let p = stPersistent s
                     in p { stCachedState = f (stCachedState p)}
    }
  forceCS

getCachedState :: TCM (Maybe (CachedState,CachedState))
getCachedState = do
  gets (stCachedState . stPersistent)

putCachedState :: (Maybe (CachedState,CachedState)) -> TCM ()
putCachedState cs = do
  modifyCachedState (const cs)

forceCS :: TCM ()
forceCS = do
  s <- get
  case s of
    TCSt { stPersistent = PersistentTCSt { stCachedState = cs } }
      -> maybe (return ()) (\ xs -> length (fst xs) `seq` length (snd xs) `seq` return ()) cs

-- | Reads the next entry in the CS, returns Nothing when empty
readCS :: TCM (Maybe (CachedDecl,LFileState))
readCS = do
  reportSLn "cache" 10 $ "readCS"
  s <- get
  let p = stPersistent s
      cs = stCachedState p
      putTail r = put (s { stPersistent = p { stCachedState = fmap (first (const r)) cs } })
  case cs of
    Just ((e:r),_w) -> do
      putTail r
      return (Just e)
    _ -> do
      return Nothing

-- | Empties the "to read" CachedState. To be used when it gets invalid.
cleanCS :: TCM ()
cleanCS = do
  reportSLn "cache" 10 $ "cleanCS"
  modifyCachedState (fmap (first (const [])))

-- | Activates caching into CachedState. Clears the written log.
activateCS :: TCM ()
activateCS = do
  reportSLn "cache" 10 $ "activateCS"
  modifyCachedState $ Just . fromMaybe ([],[]) . fmap (second (const []))

-- | Replaces the "to read" CS with the written one.
storeWrittenCS :: TCM ()
storeWrittenCS = do
  reportSLn "cache" 10 $ "storeWritten"
  modifyCachedState $ fmap (\(_r,w) -> (w,[]))
