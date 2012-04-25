{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Mutual where

import Control.Monad.Reader
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Agda.Utils.HashMap as HMap

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Fresh
import Agda.Utils.Impossible

#include "../../undefined.h"

noMutualBlock :: TCM a -> TCM a
noMutualBlock = local $ \e -> e { envMutualBlock = Nothing }

inMutualBlock :: TCM a -> TCM a
inMutualBlock m = do
  mi <- asks envMutualBlock
  case mi of
    Nothing -> do
      i <- fresh
      flip local m $ \e -> e { envMutualBlock = Just i }
    -- Don't create a new mutual block if we're already inside one.
    Just _  -> m

-- | Set the mutual block for a definition
setMutualBlock :: MutualId -> QName -> TCM ()
setMutualBlock i x = do
  modify $ \s -> s { stMutualBlocks = Map.insertWith Set.union i (Set.singleton x) $ stMutualBlocks s
		   , stSignature    = (stSignature s)
				      { sigDefinitions = setMutId x i $ sigDefinitions $ stSignature s
				      }
		   }
  where
    setMutId x i = flip HMap.adjust x $ \defn -> defn { defMutual = i }

-- | Get all mutual blocks
getMutualBlocks :: TCM [Set QName]
getMutualBlocks = gets $ Map.elems . stMutualBlocks

-- | Get the current mutual block, if any, otherwise a fresh mutual
-- block is returned.
currentOrFreshMutualBlock :: TCM MutualId
currentOrFreshMutualBlock = maybe fresh return =<< asks envMutualBlock

lookupMutualBlock :: MutualId -> TCM (Set QName)
lookupMutualBlock mi = do
  mb <- gets stMutualBlocks
  case Map.lookup mi mb of
    Just qs -> return qs
    Nothing -> return Set.empty -- can end up here if we ask for the current mutual block and there is none

findMutualBlock :: QName -> TCM (Set QName)
findMutualBlock f = do
  bs <- getMutualBlocks
  case filter (Set.member f) bs of
    []    -> fail $ "No mutual block for " ++ show f
    b : _ -> return b
