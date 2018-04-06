-- | Logic for deciding which functions should be automatically inlined.
module Agda.TypeChecking.Inlining (autoInline) where

import qualified Data.IntMap as IntMap

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Free
import Agda.Utils.Lens

-- | Mark a definition to be inlined if it satisfies the inlining criterion.
autoInline :: Defn -> Defn
autoInline defn | shouldInline defn = set funInline True defn
autoInline defn = defn

shouldInline :: Defn -> Bool
shouldInline Function{funCompiled = Just cc} = shouldInline' cc
shouldInline _ = False

-- Only auto-inline simple definitions (no pattern matching) where no variable
-- is used more than once, and some variables are not used at all.
shouldInline' :: CompiledClauses -> Bool
shouldInline' (Done xs body) = all (< 2) counts && length counts < length xs
  where counts = IntMap.elems $ varCounts $ freeVars body
shouldInline' _ = False
