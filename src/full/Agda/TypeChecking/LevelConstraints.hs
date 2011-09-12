
module Agda.TypeChecking.LevelConstraints ( simplifyLevelConstraint ) where

import Data.List

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.Utils.Size

simplifyLevelConstraint :: Integer -> Constraint -> Constraints -> Constraint
simplifyLevelConstraint n new old =
  case inequalities new of
    [a :=< b] | elem (b :=< a) leqs -> LevelCmp CmpEq (Max [a']) (Max [b'])
      where
        (a', b') = raiseFrom (-n) n (a, b)
    _ -> new
  where
    leqs = concatMap (inequalities . unClosure) old

    -- Unclosure converts deBruijn indices to deBruijn levels to
    -- enable comparing constraints under different contexts
    unClosure c = raise (-size (envContext $ clEnv cl)) $ clValue cl
      where cl = theConstraint c

data Leq = PlusLevel :=< PlusLevel
  deriving Eq

inequalities (LevelCmp CmpEq (Max [a, b]) (Max [c]))
  | a == c = [b :=< a]
  | b == c = [a :=< a]
inequalities (LevelCmp CmpEq (Max [a]) (Max [b, c]))
  | a == b = [c :=< b]
  | a == c = [b :=< c]
inequalities _ = []
