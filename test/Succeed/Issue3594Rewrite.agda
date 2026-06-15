{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

-- Adapted example from https://github.com/agda/agda/issues/3594
-- To avoid throwing an occurs check here, we need to progagate Underapplied
-- with higher priority than StuckOn

record Wrap (A : Set) : Set where
  constructor wrap
  no-eta-equality
  field
    unwrap : A

open Wrap

postulate
  P : Wrap Nat → Set

f : ∀ (y : Nat) → Wrap Nat
f 0       = wrap 0
f (suc _) = wrap 0

postulate
  f-unwrap : ∀ {y} → f y .unwrap ≡ 0
{-# REWRITE f-unwrap #-}

postulate
  q : ∀ y → P (f y)
  g : ∀ (A : Set) → (∀ (y : Nat) → A) → Nat

test = g ? (\ y → q y)
