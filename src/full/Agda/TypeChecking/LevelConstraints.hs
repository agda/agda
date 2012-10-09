
module Agda.TypeChecking.LevelConstraints ( simplifyLevelConstraint ) where

import Data.List

import Agda.Syntax.Common (Nat)
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute
import Agda.Utils.Size

-- | @simplifyLevelConstraint n c cs@ turns an @c@ into an equality
--   constraint if it is an inequality constraint and the reverse
--   inequality is contained in @cs@. Number @n@ is the length
--   of the context @c@ is defined in.
simplifyLevelConstraint :: Int -> Constraint -> Constraints -> Constraint
simplifyLevelConstraint n new old =
  case inequalities new of
    [a :=< b] | elem (b' :=< a') leqs -> LevelCmp CmpEq (Max [a]) (Max [b])
      where (a', b') = raise (waterLevel - n) (a, b)
    _ -> new
  where
    -- get the constraints plus their "waterLevels", i.e.,
    -- length of contexts they are defined in
    unClosure c = (size (envContext $ clEnv cl), clValue cl)
      where cl = theConstraint c
    (ns, ls) = unzip $ map unClosure old
    -- compute the common water level
    waterLevel :: Nat
    waterLevel = maximum (n:ns)
    -- convert deBruijn indices to deBruijn levels to
    -- enable comparing constraints under different contexts
    leqs = concatMap inequalities $ zipWith raise (map (waterLevel -) ns) ls

data Leq = PlusLevel :=< PlusLevel
  deriving (Show, Eq)

inequalities (LevelCmp CmpEq (Max [a, b]) (Max [c]))
  | a == c = [b :=< a]
  | b == c = [a :=< b]
inequalities (LevelCmp CmpEq (Max [a]) (Max [b, c]))
  | a == b = [c :=< b]
  | a == c = [b :=< c]
inequalities _ = []
