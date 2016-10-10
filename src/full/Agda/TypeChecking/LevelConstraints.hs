{-# LANGUAGE CPP #-}

module Agda.TypeChecking.LevelConstraints ( simplifyLevelConstraint ) where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Substitute ()

-- | @simplifyLevelConstraint c cs@ turns an @c@ into an equality
--   constraint if it is an inequality constraint and the reverse
--   inequality is contained in @cs@.
--
--   Precondition: all constraints live in the same context.
simplifyLevelConstraint :: Constraint -> [Constraint] -> Constraint
simplifyLevelConstraint new old =
  case inequalities new of
    [a :=< b] | elem (b :=< a) leqs -> LevelCmp CmpEq (Max [a]) (Max [b])
    _ -> new
  where
    leqs = concatMap inequalities old

data Leq = PlusLevel :=< PlusLevel
  deriving (Show, Eq)

-- | Turn a level constraint into a list of level inequalities, if possible.

inequalities :: Constraint -> [Leq]

inequalities (LevelCmp CmpLeq (Max as) (Max [b])) = map (:=< b) as  -- Andreas, 2016-09-28
  -- Why was this most natural case missing?
  -- See test/Succeed/LevelLeqGeq.agda for where it is useful!

-- These are very special cases only, in no way complete:
inequalities (LevelCmp CmpEq (Max [a, b]) (Max [c]))
  | a == c = [b :=< a]
  | b == c = [a :=< b]
inequalities (LevelCmp CmpEq (Max [a]) (Max [b, c]))
  | a == b = [c :=< b]
  | a == c = [b :=< c]
inequalities _ = []
