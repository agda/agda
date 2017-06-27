------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about subsets
------------------------------------------------------------------------

module Data.Fin.Subset.Properties where

open import Algebra
import Algebra.Properties.BooleanAlgebra as BoolProp
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; suc; zero)
open import Data.Fin.Subset
open import Data.Nat.Base using (ℕ)
open import Data.Product as Product
open import Data.Sum as Sum
open import Data.Vec hiding (_∈_)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst)
open import Relation.Nullary.Negation using (contradiction)

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
⊥⊆ x∈⊥ = contradiction x∈⊥ ∉⊥

Empty-unique : ∀ {n} {p : Subset n} → Empty p → p ≡ ⊥
Empty-unique {_} {[]}          ¬∃∈ = refl
Empty-unique {_} {inside  ∷ p} ¬∃∈ = contradiction (zero , here) ¬∃∈
Empty-unique {_} {outside ∷ p} ¬∃∈ =
  cong (outside ∷_) (Empty-unique (drop-∷-Empty ¬∃∈))

------------------------------------------------------------------------
-- Properties involving ⊤

∈⊤ : ∀ {n} {x : Fin n} → x ∈ ⊤
∈⊤ {x = zero}  = here
∈⊤ {x = suc x} = there ∈⊤

⊆⊤ : ∀ {n} {p : Subset n} → p ⊆ ⊤
⊆⊤ = const ∈⊤

------------------------------------------------------------------------
-- Properties involving ⁅_⁆

x∈⁅x⁆ : ∀ {n} (x : Fin n) → x ∈ ⁅ x ⁆
x∈⁅x⁆ zero    = here
x∈⁅x⁆ (suc x) = there (x∈⁅x⁆ x)

x∈⁅y⁆⇒x≡y : ∀ {n x} (y : Fin n) → x ∈ ⁅ y ⁆ → x ≡ y
x∈⁅y⁆⇒x≡y zero    here      = refl
x∈⁅y⁆⇒x≡y zero    (there p) = contradiction p ∉⊥
x∈⁅y⁆⇒x≡y (suc y) (there p) = cong suc (x∈⁅y⁆⇒x≡y y p)

x∈⁅y⁆⇔x≡y : ∀ {n} {x y : Fin n} → x ∈ ⁅ y ⁆ ⇔ x ≡ y
x∈⁅y⁆⇔x≡y {_} {x} {y} = equivalence
  (x∈⁅y⁆⇒x≡y y)
  (λ x≡y → subst (λ y → x ∈ ⁅ y ⁆) x≡y (x∈⁅x⁆ x))

------------------------------------------------------------------------
-- Properties involving _∪_ and _∩_

module _ {n : ℕ} where
  open BooleanAlgebra (booleanAlgebra n) public using  ()
    renaming
    ( ∨-assoc to ∪-assoc
    ; ∨-comm  to ∪-comm
    ; ∧-assoc to ∩-assoc
    ; ∧-comm  to ∩-comm
    )

-- _∪_

p⊆p∪q : ∀ {n p} (q : Subset n) → p ⊆ p ∪ q
p⊆p∪q []      ()
p⊆p∪q (s ∷ q) here        = here
p⊆p∪q (s ∷ q) (there x∈p) = there (p⊆p∪q q x∈p)

q⊆p∪q : ∀ {n} (p q : Subset n) → q ⊆ p ∪ q
q⊆p∪q p q rewrite ∪-comm p q = p⊆p∪q p

x∈p∪q⁻ :  ∀ {n} (p q : Subset n) {x} → x ∈ p ∪ q → x ∈ p ⊎ x ∈ q
x∈p∪q⁻ []            []            ()
x∈p∪q⁻ (inside  ∷ p) (t       ∷ q) here          = inj₁ here
x∈p∪q⁻ (outside ∷ p) (inside  ∷ q) here          = inj₂ here
x∈p∪q⁻ (s       ∷ p) (t       ∷ q) (there x∈p∪q) =
  Sum.map there there (x∈p∪q⁻ p q x∈p∪q)

x∈p∪q⁺ : ∀ {n} {p q : Subset n} {x} → x ∈ p ⊎ x ∈ q → x ∈ p ∪ q
x∈p∪q⁺ (inj₁ x∈p) = p⊆p∪q _   x∈p
x∈p∪q⁺ (inj₂ x∈q) = q⊆p∪q _ _ x∈q

∪⇔⊎ : ∀ {n} {p q : Subset n} {x} → x ∈ p ∪ q ⇔ (x ∈ p ⊎ x ∈ q)
∪⇔⊎ = equivalence (x∈p∪q⁻ _ _) x∈p∪q⁺

-- _∩_

p∩q⊆p : ∀ {n} (p q : Subset n) → p ∩ q ⊆ p
p∩q⊆p [] [] x∈p∩q = x∈p∩q
p∩q⊆p (inside  ∷ p) (inside  ∷ q) here = here
p∩q⊆p (inside  ∷ p) (inside  ∷ q) (there ∈p∩q) = there (p∩q⊆p p q ∈p∩q)
p∩q⊆p (outside ∷ p) (inside  ∷ q) (there ∈p∩q) = there (p∩q⊆p p q ∈p∩q)
p∩q⊆p (inside  ∷ p) (outside ∷ q) (there ∈p∩q) = there (p∩q⊆p p q ∈p∩q)
p∩q⊆p (outside ∷ p) (outside ∷ q) (there ∈p∩q) = there (p∩q⊆p p q ∈p∩q)

p∩q⊆q : ∀ {n} (p q : Subset n) → p ∩ q ⊆ q
p∩q⊆q p q rewrite ∩-comm p q = p∩q⊆p q p

x∈p∩q⁺ : ∀ {n} {p q : Subset n} {x} → x ∈ p × x ∈ q → x ∈ p ∩ q
x∈p∩q⁺ (here , here) = here
x∈p∩q⁺ (there x∈p , there x∈q) = there (x∈p∩q⁺ (x∈p , x∈q))

x∈p∩q⁻ : ∀ {n} (p q : Subset n) {x} → x ∈ p ∩ q → x ∈ p × x ∈ q
x∈p∩q⁻ [] [] ()
x∈p∩q⁻ (inside ∷ p) (inside ∷ q) here = here , here
x∈p∩q⁻ (s      ∷ p) (t      ∷ q) (there x∈p∩q) =
  Product.map there there (x∈p∩q⁻ p q x∈p∩q)

∩⇔× : ∀ {n} {p q : Subset n} {x} → x ∈ p ∩ q ⇔ (x ∈ p × x ∈ q)
∩⇔× = equivalence (x∈p∩q⁻ _ _) x∈p∩q⁺

------------------------------------------------------------------------
-- _⊆_ is a partial order

-- The "natural poset" associated with the boolean algebra.

module NaturalPoset where
  private
    open module BA {n} = BoolProp (booleanAlgebra n) public
      using (poset)
    open module Po {n} = Poset (poset {n = n}) public hiding (refl)

  -- _⊆_ is equivalent to the natural lattice order.

  orders-equivalent : ∀ {n} {p₁ p₂ : Subset n} → p₁ ⊆ p₂ ⇔ p₁ ≤ p₂
  orders-equivalent = equivalence (to _ _) (from _ _)
    where
    to : ∀ {n} (p₁ p₂ : Subset n) → p₁ ⊆ p₂ → p₁ ≤ p₂
    to []             []             p₁⊆p₂ = refl
    to (inside  ∷ p₁) (_       ∷ p₂) p₁⊆p₂ with p₁⊆p₂ here
    to (inside  ∷ p₁) (.inside ∷ p₂) p₁⊆p₂ | here = cong (_∷_ inside)  (to p₁ p₂ (drop-∷-⊆ p₁⊆p₂))
    to (outside ∷ p₁) (_       ∷ p₂) p₁⊆p₂        = cong (_∷_ outside) (to p₁ p₂ (drop-∷-⊆ p₁⊆p₂))

    from : ∀ {n} (p₁ p₂ : Subset n) → p₁ ≤ p₂ → p₁ ⊆ p₂
    from []             []       p₁≤p₂ x               = x
    from (.inside ∷ _)  (_ ∷ _)  p₁≤p₂ here            rewrite cong head p₁≤p₂ = here
    from (_       ∷ p₁) (_ ∷ p₂) p₁≤p₂ (there xs[i]=x) =
      there (from p₁ p₂ (cong tail p₁≤p₂) xs[i]=x)

-- _⊆_ is a partial order.

poset : ℕ → Poset _ _ _
poset n = record
  { Carrier        = Subset n
  ; _≈_            = _≡_
  ; _≤_            = _⊆_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = isEquivalence
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
