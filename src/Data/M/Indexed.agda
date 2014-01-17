------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed M-types (the dual of indexed W-types aka Petersson-Synek
-- trees).
------------------------------------------------------------------------

module Data.M.Indexed where

open import Level
open import Coinduction
open import Data.Product
open import Data.Container.Indexed.Core
open import Function
open import Relation.Unary

-- The family of indexed M-types.

module _ {ℓ c r} {O : Set ℓ} (C : Container O O c r) where

  data M (o : O) : Set (ℓ ⊔ c ⊔ r) where
    inf : ⟦ C ⟧ (∞ ∘ M) o → M o

  open Container C

  -- Projections.

  head : M ⊆ Command
  head (inf (c , _)) = c

  tail : ∀ {o} (m : M o) (r : Response (head m)) → M (next (head m) r)
  tail (inf (_ , k)) r = ♭ (k r)

  force : M ⊆ ⟦ C ⟧ M
  force (inf (c , k)) = c , λ r → ♭ (k r)

  -- Coiteration.

  coit : ∀ {ℓ} {X : Pred O ℓ} → X ⊆ ⟦ C ⟧ X → X ⊆ M
  coit ψ x = inf (proj₁ cs , λ r → ♯ coit ψ (proj₂ cs r))
    where
    cs = ψ x
