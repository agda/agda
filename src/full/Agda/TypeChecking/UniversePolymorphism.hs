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

compareLevel :: Comparison -> Level -> Level -> TCM ()
compareLevel CmpLeq u v = leqLevel u v
compareLevel CmpEq  u v = equalLevel u v

isLevelConstraint LevelCmp{} = True
isLevelConstraint _          = False
