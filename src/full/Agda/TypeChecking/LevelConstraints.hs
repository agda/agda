
module Agda.TypeChecking.LevelConstraints ( simplifyLevelConstraints ) where

import Data.List

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.Utils.Size

simplifyLevelConstraints :: Constraints -> Constraints -> Constraints
simplifyLevelConstraints new old = simplify lcs oldlcs ++ other
  where
    oldlcs = filter (isLevelConstraint . clValue) old
    (lcs, other) = partition (isLevelConstraint . clValue) new

    isLevelConstraint LevelCmp{} = True
    isLevelConstraint _          = False

simplify lcs oldlcs = map simpl lcs
  where
    leqs = concatMap (inequalities . unClosure) oldlcs

    simpl c = case inequalities (unClosure c) of
      [a :=< b] | elem (b :=< a) leqs ->
        c { clValue = LevelCmp CmpEq (Max [a']) (Max [b']) }
        where
          n        = size $ envContext $ clEnv c
          (a', b') = raiseFrom (-n) n (a, b)
      _ -> c

    -- Unclosure converts deBruijn indices to deBruijn levels to
    -- enable comparing constraints under different contexts
    unClosure cl = raise (-size (envContext $ clEnv cl)) $ clValue cl

data Leq = PlusLevel :=< PlusLevel
  deriving Eq

inequalities (LevelCmp CmpEq (Max [a, b]) (Max [c]))
  | a == c = [b :=< a]
  | b == c = [a :=< a]
inequalities (LevelCmp CmpEq (Max [a]) (Max [b, c]))
  | a == b = [c :=< b]
  | a == c = [b :=< c]
inequalities _ = []
