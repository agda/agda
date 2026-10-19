-- Andreas, 2026-08-29, issue #8696
-- Issue found by Claude and reported by bdrisc-ant

-- The same overwritten occurrence observed through polarity: the index of the
-- copied N.IsZ became Nonvariant, and --lossy-unification's first-order
-- shortcut then identified  N.IsZ 0  and  N.IsZ 1.

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data ⊥ : Set where

module M (A : Set) where
  data IsZ : Nat → Set where
    isz : IsZ zero

mutual
  data Dummy : Set where
    mkD : Dummy
  module N = M ⊥

cast : N.IsZ 0 ≡ N.IsZ 1
cast = refl

coe : {A B : Set} → A ≡ B → A → B
coe refl x = x

no : N.IsZ 1 → ⊥
no ()

boom : ⊥
boom = no (coe cast N.isz)
