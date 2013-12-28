-- RETIRED (Andreas, 2013-12-28)

-- {-# LANGUAGE CPP #-}

module Agda.TypeChecking.UniversePolymorphism where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Conversion

-- MOVED to Conversion
-- compareLevel :: Comparison -> Level -> Level -> TCM ()
-- compareLevel CmpLeq u v = leqLevel u v
-- compareLevel CmpEq  u v = equalLevel u v

isLevelConstraint LevelCmp{} = True
isLevelConstraint _          = False
