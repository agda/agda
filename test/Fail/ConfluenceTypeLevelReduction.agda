-- Jesper, 2019-05-20: When checking confluence of two rewrite rules,
-- we disable all reductions during unification of the left-hand
-- sides. However, we should not disable reductions at the type-level,
-- as shown by this (non-confluent) example.

{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data Unit : Set where unit : Unit

A : Unit → Set
A unit = ⊤

postulate
  a b : (u : Unit) → A u
  f : (u : Unit) → A u → Bool
  f-a : (u : Unit) → f u (a u) ≡ true
  f-b : (u : Unit) → f u (b u) ≡ false

{-# REWRITE f-a #-}
{-# REWRITE f-b #-}

cong-f : (u : Unit) (x y : A u) → x ≡ y → f u x ≡ f u y
cong-f u x y refl = refl

boom : true ≡ false
boom = cong-f unit (a unit) (b unit) refl
