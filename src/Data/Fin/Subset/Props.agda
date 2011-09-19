------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about subsets
------------------------------------------------------------------------

module Data.Fin.Subset.Props where

open import Algebra
import Algebra.Props.BooleanAlgebra as BoolProp
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin); open Data.Fin.Fin
open import Data.Fin.Subset
open import Data.Nat using (ℕ)
open import Data.Product
open import Data.Sum as Sum
open import Data.Vec hiding (_∈_)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Constructor mangling

drop-there : ∀ {s n x} {p : Subset n} → suc x ∈ s ∷ p → x ∈ p
drop-there (there x∈p) = x∈p

drop-∷-⊆ : ∀ {n s₁ s₂} {p₁ p₂ : Subset n} → s₁ ∷ p₁ ⊆ s₂ ∷ p₂ → p₁ ⊆ p₂
drop-∷-⊆ p₁s₁⊆p₂s₂ x∈p₁ = drop-there $ p₁s₁⊆p₂s₂ (there x∈p₁)

drop-∷-Empty : ∀ {n s} {p : Subset n} → Empty (s ∷ p) → Empty p
drop-∷-Empty ¬∃∈ (x , x∈p) = ¬∃∈ (suc x , there x∈p)

------------------------------------------------------------------------
-- Properties involving ⊥

∉⊥ : ∀ {n} {x : Fin n} → x ∉ ⊥
∉⊥ (there p) = ∉⊥ p

⊥⊆ : ∀ {n} {p : Subset n} → ⊥ ⊆ p
⊥⊆ x∈⊥ with ∉⊥ x∈⊥
... | ()

Empty-unique : ∀ {n} {p : Subset n} →
               Empty p → p ≡ ⊥
Empty-unique {p = []}           ¬∃∈ = P.refl
Empty-unique {p = s ∷ p}        ¬∃∈ with Empty-unique (drop-∷-Empty ¬∃∈)
Empty-unique {p = outside ∷ .⊥} ¬∃∈ | P.refl = P.refl
Empty-unique {p = inside  ∷ .⊥} ¬∃∈ | P.refl =
  ⊥-elim (¬∃∈ (zero , here))

------------------------------------------------------------------------
-- Properties involving ⊤

∈⊤ : ∀ {n} {x : Fin n} → x ∈ ⊤
∈⊤ {x = zero}  = here
∈⊤ {x = suc x} = there ∈⊤

⊆⊤ : ∀ {n} {p : Subset n} → p ⊆ ⊤
⊆⊤ = const ∈⊤

------------------------------------------------------------------------
-- A property involving ⁅_⁆

x∈⁅y⁆⇔x≡y : ∀ {n} {x y : Fin n} → x ∈ ⁅ y ⁆ ⇔ x ≡ y
x∈⁅y⁆⇔x≡y {x = x} {y} =
  equivalence (to y) (λ x≡y → P.subst (λ y → x ∈ ⁅ y ⁆) x≡y (x∈⁅x⁆ x))
  where

  to : ∀ {n x} (y : Fin n) → x ∈ ⁅ y ⁆ → x ≡ y
  to (suc y) (there p) = P.cong suc (to y p)
  to zero    here      = P.refl
  to zero    (there p) with ∉⊥ p
  ... | ()

  x∈⁅x⁆ : ∀ {n} (x : Fin n) → x ∈ ⁅ x ⁆
  x∈⁅x⁆ zero    = here
  x∈⁅x⁆ (suc x) = there (x∈⁅x⁆ x)

------------------------------------------------------------------------
-- A property involving _∪_

∪⇔⊎ : ∀ {n} {p₁ p₂ : Subset n} {x} → x ∈ p₁ ∪ p₂ ⇔ (x ∈ p₁ ⊎ x ∈ p₂)
∪⇔⊎ = equivalence (to _ _) from
  where
  to : ∀ {n} (p₁ p₂ : Subset n) {x} → x ∈ p₁ ∪ p₂ → x ∈ p₁ ⊎ x ∈ p₂
  to []             []             ()
  to (inside  ∷ p₁) (s₂      ∷ p₂) here            = inj₁ here
  to (outside ∷ p₁) (inside  ∷ p₂) here            = inj₂ here
  to (s₁      ∷ p₁) (s₂      ∷ p₂) (there x∈p₁∪p₂) =
    Sum.map there there (to p₁ p₂ x∈p₁∪p₂)

  ⊆∪ˡ : ∀ {n p₁} (p₂ : Subset n) → p₁ ⊆ p₁ ∪ p₂
  ⊆∪ˡ []       ()
  ⊆∪ˡ (s ∷ p₂) here         = here
  ⊆∪ˡ (s ∷ p₂) (there x∈p₁) = there (⊆∪ˡ p₂ x∈p₁)

  ⊆∪ʳ : ∀ {n} (p₁ p₂ : Subset n) → p₂ ⊆ p₁ ∪ p₂
  ⊆∪ʳ p₁ p₂ rewrite BooleanAlgebra.∨-comm (booleanAlgebra _) p₁ p₂
    = ⊆∪ˡ p₁

  from : ∀ {n} {p₁ p₂ : Subset n} {x} → x ∈ p₁ ⊎ x ∈ p₂ → x ∈ p₁ ∪ p₂
  from (inj₁ x∈p₁) = ⊆∪ˡ _   x∈p₁
  from (inj₂ x∈p₂) = ⊆∪ʳ _ _ x∈p₂

------------------------------------------------------------------------
-- _⊆_ is a partial order

-- The "natural poset" associated with the boolean algebra.

module NaturalPoset where
  private
    open module BA {n} = BoolProp (booleanAlgebra n) public
      using (poset)
    open module Po {n} = Poset (poset {n = n}) public

  -- _⊆_ is equivalent to the natural lattice order.

  orders-equivalent : ∀ {n} {p₁ p₂ : Subset n} → p₁ ⊆ p₂ ⇔ p₁ ≤ p₂
  orders-equivalent = equivalence (to _ _) (from _ _)
    where
    to : ∀ {n} (p₁ p₂ : Subset n) → p₁ ⊆ p₂ → p₁ ≤ p₂
    to []             []             p₁⊆p₂ = P.refl
    to (inside  ∷ p₁) (_       ∷ p₂) p₁⊆p₂ with p₁⊆p₂ here
    to (inside  ∷ p₁) (.inside ∷ p₂) p₁⊆p₂ | here = P.cong (_∷_ inside)  (to p₁ p₂ (drop-∷-⊆ p₁⊆p₂))
    to (outside ∷ p₁) (_       ∷ p₂) p₁⊆p₂        = P.cong (_∷_ outside) (to p₁ p₂ (drop-∷-⊆ p₁⊆p₂))

    from : ∀ {n} (p₁ p₂ : Subset n) → p₁ ≤ p₂ → p₁ ⊆ p₂
    from []             []       p₁≤p₂ x               = x
    from (.inside ∷ _)  (_ ∷ _)  p₁≤p₂ here            rewrite P.cong head p₁≤p₂ = here
    from (_       ∷ p₁) (_ ∷ p₂) p₁≤p₂ (there xs[i]=x) =
      there (from p₁ p₂ (P.cong tail p₁≤p₂) xs[i]=x)

-- _⊆_ is a partial order.

poset : ℕ → Poset _ _ _
poset n = record
  { Carrier        = Subset n
  ; _≈_            = _≡_
  ; _≤_            = _⊆_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = P.isEquivalence
      ; reflexive     = λ i≡j → from ⟨$⟩ reflexive i≡j
      ; trans         = λ x⊆y y⊆z → from ⟨$⟩ trans (to ⟨$⟩ x⊆y) (to ⟨$⟩ y⊆z)
      }
    ; antisym = λ x⊆y y⊆x → antisym (to ⟨$⟩ x⊆y) (to ⟨$⟩ y⊆x)
    }
  }
  where
  open NaturalPoset
  open module E {p₁ p₂} =
    Equivalence (orders-equivalent {n = n} {p₁ = p₁} {p₂ = p₂})
