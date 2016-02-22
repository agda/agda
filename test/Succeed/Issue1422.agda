module Issue1422 where

open import Common.Level public using (Level ; lzero ; lsuc) renaming (_⊔_ to _l⊔_)
open import Common.Equality public

-- # Relations

relation : ∀ {ℓ} ℓ' → Set ℓ → Set (lsuc ℓ' l⊔ ℓ)
relation ℓ' α = α → α → Set ℓ'

reflexive : ∀ {ℓ ℓ'} {α : Set ℓ} → relation ℓ' α → Set (ℓ l⊔ ℓ')
reflexive _R_ = ∀ {x} → x R x

antisymmetric : ∀ {ℓ ℓ'} {α : Set ℓ} → relation ℓ' α → Set (ℓ l⊔ ℓ')
antisymmetric _R_ = ∀ {x y} → x R y → y R x → x ≡ y

_⇉_ : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} {α : Set ℓ₁} {β : Set ℓ₂} (_R₁_ : relation ℓ₁' α) (_R₂_ : relation ℓ₂' β) → relation (ℓ₁ l⊔ ℓ₁' l⊔ ℓ₂') (α → β)
(_R₁_ ⇉ _R₂_) f g = ∀ {x y} → x R₁ y → f x R₂ g y

proper : ∀ {ℓ ℓ'} {α : Set ℓ} (_R_ : relation ℓ' α) → α → Set ℓ'
proper _R_ x = x R x

-- # Dom

record Dom {ℓ} ℓ' (D : Set ℓ) : Set (lsuc ℓ l⊔ lsuc ℓ') where
  field
    ⟦_⟧ : D → Set ℓ'
open Dom {{...}} public

-- # Partial Order

record PartialOrder {ℓ} ℓ' (α : Set ℓ) : Set (ℓ l⊔ lsuc ℓ') where
  infix  4 _⊑_
  field
    _⊑_ : relation ℓ' α
    ⊑-reflexivity : reflexive _⊑_
    ⊑-antisymmetry : antisymmetric _⊑_

open PartialOrder {{...}} public

monotonic : ∀ {ℓ₁ ℓ₁' ℓ₂ ℓ₂'} {α : Set ℓ₁} {{αPO : PartialOrder ℓ₁' α}} {β : Set ℓ₂} {{βPO : PartialOrder ℓ₂' β}} → (α → β) → Set (ℓ₁ l⊔ ℓ₁' l⊔ ℓ₂')
monotonic = proper (_⊑_ ⇉ _⊑_)
