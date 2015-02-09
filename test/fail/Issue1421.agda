-- Andreas, 2015-02-09, issue reported by David Darais

-- {-# OPTIONS -v tc.with.infer:100 #-}
-- {-# OPTIONS -v impossible:100 #-}
-- {-# OPTIONS -v import.metas:10 #-}

module Issue1421 where

open import Issue1421.Lib as Core

-- # POSet
--
-- POSets are like Agda Sets only they come equipped with a partial
-- order. This is so structures like Monad can be in the category of
-- POSets (rather than Set). This makes it much easier than threading
-- {{PartialOrder}} type class constraints around.

record POSet ℓ ℓ' : Set (lsuc ℓ l⊔ lsuc ℓ') where
  constructor [⊑_,_]
  field
    POSet⟦_⟧ : Set ℓ
    POSet-PartialOrder : PartialOrder ℓ' POSet⟦_⟧
open POSet public

instance
  POSet-Dom : ∀ {ℓ ℓ'} → Dom ℓ (POSet ℓ ℓ')
  POSet-Dom = record { ⟦_⟧ = POSet⟦_⟧ }

-- # Nat
--
-- A very simple example of constructing a POSet. The [Nat] POSet is
-- interpreted as the nat Set from Core.agda, and uses the partial
-- order defined for nat in Core.agda.

Nat : POSet lzero lzero
Nat = [⊑ nat , nat-PartialOrder ]

-- # Monotonic Function Space

_⇒_ : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} → (α : POSet ℓ₁ ℓ₁') (β : POSet ℓ₂ ℓ₂') → POSet (ℓ₁ l⊔ ℓ₁' l⊔ ℓ₂ l⊔ ℓ₂') (ℓ₁ l⊔ ℓ₁' l⊔ ℓ₂')
[⊑ α , αPO ] ⇒ [⊑ β , βPO ] = [⊑ α Core.↗ β , ↗-PartialOrder ]

record fuel {ℓ ℓ'} (m : POSet ℓ ℓ' → POSet ℓ ℓ') (α : POSet ℓ ℓ') : Set (ℓ l⊔ ℓ') where
  constructor mk-fuel
  field
    fuel-f : ⟦ Nat ⇒ m α ⟧
open fuel

_fuel-⊑_ : ∀ {ℓ ℓ'} {m : POSet ℓ ℓ' → POSet ℓ ℓ'} {α : POSet ℓ ℓ'} → relation ℓ' (fuel m α)
_fuel-⊑_ aM₁ aM₂ = fuel-f aM₁ ⊑ fuel-f aM₂

fuel-⊑-antisymmetry : ∀ {ℓ ℓ'} {m : POSet ℓ ℓ' → POSet ℓ ℓ'} {α : POSet ℓ ℓ'} →
  antisymmetric (_fuel-⊑_ {m = m} {α = α})
fuel-⊑-antisymmetry {x = mk-fuel f} {y = mk-fuel g} f⊑g g⊑h
  rewrite ⊑-antisymmetry {x = f} {y = g} f⊑g g⊑h = refl

-- This rewrite generates some unresolve instance metas.
-- They should point to the current file, not to Issue1421.Lib
