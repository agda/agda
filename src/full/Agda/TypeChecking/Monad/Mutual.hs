-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Mutual where

import Prelude hiding (null)

import Control.Monad.Reader

import Data.Functor ((<$>))
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Agda.Syntax.Info as Info
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State

import Agda.Utils.Lens
import Agda.Utils.Null
import Agda.Utils.Pretty ( prettyShow )

noMutualBlock :: TCM a -> TCM a
noMutualBlock = local $ \e -> e { envMutualBlock = Nothing }

-- | Pass the current mutual block id
--   or create a new mutual block if we are not already inside on.
inMutualBlock :: (MutualId -> TCM a) -> TCM a
inMutualBlock m = do
  mi <- asks envMutualBlock
  case mi of
    Nothing -> do
      i <- fresh
      local (\ e -> e { envMutualBlock = Just i }) $ m i
    -- Don't create a new mutual block if we're already inside one.
    Just i -> m i

-- | Set the mutual block info for a block,
--   possibly overwriting the existing one.

setMutualBlockInfo :: MutualId -> Info.MutualInfo -> TCM ()
setMutualBlockInfo mi info = stMutualBlocks %= Map.alter f mi
  where
  f Nothing                   = Just $ MutualBlock info empty
  f (Just (MutualBlock _ xs)) = Just $ MutualBlock info xs

-- | Set the mutual block info for a block if non-existing.

insertMutualBlockInfo :: MutualId -> Info.MutualInfo -> TCM ()
insertMutualBlockInfo mi info = stMutualBlocks %= Map.alter f mi
  where
  f Nothing = Just $ MutualBlock info empty
  f (Just mb@(MutualBlock info0 xs))
    | null info0 = Just $ MutualBlock info xs
    | otherwise  = Just mb

-- | Set the mutual block for a definition.

setMutualBlock :: MutualId -> QName -> TCM ()
setMutualBlock i x = do
  stMutualBlocks %= Map.alter f i
  stSignature    %= updateDefinition x (\ defn -> defn { defMutual = i })
  where
  f Nothing                    = Just $ MutualBlock empty $ Set.singleton x
  f (Just (MutualBlock mi xs)) = Just $ MutualBlock mi $ Set.insert x xs

-- | Get the current mutual block, if any, otherwise a fresh mutual
-- block is returned.
currentOrFreshMutualBlock :: TCM MutualId
currentOrFreshMutualBlock = maybe fresh return =<< asks envMutualBlock

lookupMutualBlock :: MutualId -> TCM MutualBlock
lookupMutualBlock mi = do
  mbs <- use stMutualBlocks
  case Map.lookup mi mbs of
    Just mb -> return mb
    Nothing -> return empty -- can end up here if we ask for the current mutual block and there is none

-- | Reverse lookup of a mutual block id for a names.
mutualBlockOf :: QName -> TCM MutualId
mutualBlockOf x = do
  mb <- Map.toList <$> use stMutualBlocks
  case filter (Set.member x . mutualNames . snd) mb of
    (i, _) : _ -> return i
    _          -> fail $ "No mutual block for " ++ prettyShow x
