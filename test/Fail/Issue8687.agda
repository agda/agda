-- Andreas, 2026-08-27, issue #8687
-- Report and test case by @bdrisc-ant, attributed to Claude

-- Incorrect context for missing clause inferred by the coverage checker
-- (wrong weakening).

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data ⊥ : Set where

it : {A : Set} {{a : A}} → A
it {{a}} = a

record C : Set where
  field
    k : Nat
    p : k ≡ 0

record P : Set where
  field
    v : Nat
    ⦃ i ⦄ : C

module M (n : Nat) (q : n ≡ 0) where

  instance
    c : C
    c = record { k = n ; p = q }

  f : (b : Bool) → P
  f b = λ where
    .P.v → 0
    -- .P.i case omitted: inferred by instance search
    -- .P.i → it  -- Adding this clause removes the problem

bad : C.k (P.i (M.f 0 refl true)) ≡ 0 → ⊥  -- the domain normalizes to `true ≡ 0`
bad ()

boom : ⊥
boom = bad (C.p (P.i (M.f 0 refl true)))

-- Expected error: [ShouldBeEmpty]
-- C.k (P.i (M.f 0 refl true)) ≡ 0 should be empty, but the following
-- constructor patterns are valid:
--   refl
-- when checking the clause left hand side
-- bad ()
