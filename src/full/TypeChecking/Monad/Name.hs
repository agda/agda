{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecking.Monad.Name where

import Control.Monad.Reader
import Control.Monad.State
import Data.List as L
import Data.Map as M

import Utils.Monad
import Utils.Fresh

import Syntax.Common
import Syntax.Position
import Syntax.Concrete.Name as CN
import Syntax.Abstract.Name as AN

import TypeChecking.Monad

#include "../../undefined.h"


-- | TODO: how does this relate to what's in "Syntax.Translation.AbstractToConcrete"?
refreshName :: Range -> String -> TCM AN.Name
refreshName r s = do
   s' <- snd . (`refreshStr` s) <$> takenNameStr
   i <- fresh
   return $ AN.Name i (CN.Name r [Id s'])

refreshName_ = refreshName noRange

takenNameStr :: TCM [String]
takenNameStr = do
  xss <- sequence [ L.map fst <$> getContext
                  , keys <$> asks envLetBindings
                  , M.fold ((++) . keys . mdefDefs) [] <$> getSignature]
  return $ concat [ parts x | AN.Name _ x <- concat xss]
  where
    parts (CN.Name _ ps) = [ s | Id s <- ps ]

refreshStr :: [String] -> String -> ([String], String)
refreshStr taken s = go nameModifiers where
  go (m:mods) = let s' = s ++ m in
                if s' `elem` taken then go mods else (s':taken, s')
  go _        = __IMPOSSIBLE__

nameModifiers = "" : "'" : "''" : [show i | i <-[3..]]

refreshStrs = mapAccumL refreshStr
