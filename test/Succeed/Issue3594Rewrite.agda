{-# OPTIONS --rewriting --allow-unsolved-metas #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Nat

-- Adapted example from https://github.com/agda/agda/issues/3594
-- To avoid throwing an occurs error here, we need to correctly return
-- 'Underapplied' from the rewrite rule matching and prioritise 'Underapplied'
-- over 'StuckOn'

record Wrap (A : Set) : Set where
  constructor wrap
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

-- Can fill with 'P (wrap 0)'
test = g ? (\ y → q y)
