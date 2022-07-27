-- Andreas, 2022-07-12, issue #5989 reported by j-towns
--
-- The use of a private macro in a tactic annotation
-- produced an internal error when the private macro
-- was removed by dead code elimination.
--
-- Reason: names in tactic arguments were not tracked.

{-# OPTIONS -v impossible:10 #-}

module Issue5989 where

open import Agda.Builtin.Nat
open import Issue5989.Import

two : Nat
two = use-tactic 2

-- Should succeed without error.
