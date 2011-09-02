
module Agda.TypeChecking.LevelConstraints ( simplifyLevelConstraints ) where

import Data.List

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

simplifyLevelConstraints :: Constraints -> Constraints
simplifyLevelConstraints cs = simplify lcs ++ other
  where
    (lcs, other) = partition (isLevelConstraint . clValue) cs

    isLevelConstraint LevelCmp{} = True
    isLevelConstraint _          = False

simplify lcs = map simpl lcs
  where
    leqs = concatMap (inequalities . clValue) lcs

    simpl c = case inequalities (clValue c) of
      [a :=< b] | elem (b :=< a) leqs -> c { clValue = LevelCmp CmpEq (Max [a]) (Max [b]) }
      _                               -> c

data Leq = PlusLevel :=< PlusLevel
  deriving Eq

inequalities (LevelCmp CmpEq (Max [a, b]) (Max [c]))
  | a == c = [b :=< a]
  | b == c = [a :=< a]
inequalities (LevelCmp CmpEq (Max [a]) (Max [b, c]))
  | a == b = [c :=< b]
  | a == c = [b :=< c]
inequalities _ = []

