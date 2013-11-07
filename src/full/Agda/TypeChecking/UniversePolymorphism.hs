-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.UniversePolymorphism where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion

compareLevel :: Comparison -> Level -> Level -> TCM ()
compareLevel CmpLeq u v = leqLevel u v
compareLevel CmpEq  u v = equalLevel u v

isLevelConstraint LevelCmp{} = True
isLevelConstraint _          = False
