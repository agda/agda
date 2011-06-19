{-# LANGUAGE CPP #-}

module Agda.TypeChecking.UniversePolymorphism where

import Control.Applicative
import Control.Monad.Error
import Data.List

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Level
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Conversion
import qualified Agda.Utils.Warshall as W

import Agda.Utils.Impossible

#include "../undefined.h"

compareLevel :: MonadTCM tcm => Comparison -> Level -> Level -> tcm Constraints
compareLevel CmpLeq u v = leqLevel u v
compareLevel CmpEq  u v = equalLevel u v

isLevelConstraint LevelCmp{} = True
isLevelConstraint _          = False

warshallConstraint :: Constraint -> TCM [W.Constraint]
warshallConstraint (LevelCmp cmp a b) = do
  -- produce constraints
  return []
warshallConstraint _ = __IMPOSSIBLE__

solveLevelConstraints :: TCM ()
solveLevelConstraints = do
  cs <- takeConstraints
  let (lcs, rest) = partition (isLevelConstraint . clValue) cs

  lcs <- concat <$> mapM warshallConstraint (map clValue lcs)

  let msol = W.solve lcs

  case msol of
    Nothing  -> typeError $ GenericError "Bad universe levels! No further information provided. You suck!"
    Just sol -> do
      -- do something interesting with the solution
      addConstraints rest
      return ()
