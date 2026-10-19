-- Andreas, 2016-06-03, bug found by Ulf
-- {-# OPTIONS -v tc.cover:20 #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst
open Σ

record ⊤ : Set where
data ⊥ : Set where

T : Bool → Set
T true = ⊤
T false = ⊥

p : Σ Bool T
fst p = false
p = true , _

loop : ⊥
loop = snd p

-- Andreas, 2025-10-25, issue #8139
-- WAS:  error: [SplitError.CosplitCatchall]
-- Cannot split into projections because not all clauses have a
-- projection copattern
--
-- NOW:  error: [CoverageIssue]
-- Incomplete pattern matching for p. Missing cases:
--   p .snd
-- when checking the definition of p
-- ———— Warnings ——————————————————————————————————————————————
-- warning: -W[no]UnreachableClauses
-- Unreachable clause
-- when checking the definition of p
