{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
#endif

module Agda.TypeChecking.LevelConstraints ( simplifyLevelConstraint ) where

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
    -- raise deBruijn indices to largest context to
    -- enable comparing constraints under different contexts
    leqs = concatMap inequalities $ zipWith raise (map (waterLevel -) ns) ls

data Leq = PlusLevel :=< PlusLevel
  deriving (Show, Eq)

inequalities :: Constraint -> [Leq]
inequalities (LevelCmp CmpEq (Max [a, b]) (Max [c]))
  | a == c = [b :=< a]
  | b == c = [a :=< b]
inequalities (LevelCmp CmpEq (Max [a]) (Max [b, c]))
  | a == b = [c :=< b]
  | a == c = [b :=< c]
inequalities _ = []
