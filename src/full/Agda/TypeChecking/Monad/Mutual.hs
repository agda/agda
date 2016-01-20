-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Mutual where

import Control.Monad.Reader

import qualified Data.Map as Map
import Data.Set (Set)
import Data.Functor ((<$>))
import qualified Data.Set as Set

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State

import Agda.Utils.Lens

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
  stMutualBlocks %= Map.insertWith Set.union i (Set.singleton x)
  stSignature    %= updateDefinition x (\ defn -> defn { defMutual = i })

-- | Get all mutual blocks
getMutualBlocks :: TCM [Set QName]
getMutualBlocks = Map.elems <$> use stMutualBlocks

-- | Get the current mutual block, if any, otherwise a fresh mutual
-- block is returned.
currentOrFreshMutualBlock :: TCM MutualId
currentOrFreshMutualBlock = maybe fresh return =<< asks envMutualBlock

lookupMutualBlock :: MutualId -> TCM (Set QName)
lookupMutualBlock mi = do
  mb <- use stMutualBlocks
  case Map.lookup mi mb of
    Just qs -> return qs
    Nothing -> return Set.empty -- can end up here if we ask for the current mutual block and there is none

mutualBlockOf :: QName -> TCM MutualId
mutualBlockOf x = do
  mb <- Map.toList <$> use stMutualBlocks
  case filter (Set.member x . snd) mb of
    (i, _) : _ -> return i
    _          -> fail $ "No mutual block for " ++ show x

findMutualBlock :: QName -> TCM (Set QName)
findMutualBlock f = do
  bs <- getMutualBlocks
  case filter (Set.member f) bs of
    []    -> fail $ "No mutual block for " ++ show f
    b : _ -> return b
