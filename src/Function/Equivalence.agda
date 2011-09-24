------------------------------------------------------------------------
-- The Agda standard library
--
-- Equivalence (coinhabitance)
------------------------------------------------------------------------

module Function.Equivalence where

open import Function using (flip)
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_) renaming (_∘_ to _⟪∘⟫_)
open import Level
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

-- Setoid equivalence.

record Equivalence {f₁ f₂ t₁ t₂}
                   (From : Setoid f₁ f₂) (To : Setoid t₁ t₂) :
                   Set (f₁ ⊔ f₂ ⊔ t₁ ⊔ t₂) where
  field
    to   : From ⟶ To
    from : To ⟶ From

-- Set equivalence.

infix 3 _⇔_

_⇔_ : ∀ {f t} → Set f → Set t → Set _
From ⇔ To = Equivalence (P.setoid From) (P.setoid To)

equivalence : ∀ {f t} {From : Set f} {To : Set t} →
              (From → To) → (To → From) → From ⇔ To
equivalence to from = record { to = P.→-to-⟶ to; from = P.→-to-⟶ from }

------------------------------------------------------------------------
-- Map and zip

map : ∀ {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂}
        {f₁′ f₂′ t₁′ t₂′}
        {From′ : Setoid f₁′ f₂′} {To′ : Setoid t₁′ t₂′} →
      ((From ⟶ To) → (From′ ⟶ To′)) →
      ((To ⟶ From) → (To′ ⟶ From′)) →
      Equivalence From To → Equivalence From′ To′
map t f eq = record { to = t to; from = f from }
  where open Equivalence eq

zip : ∀ {f₁₁ f₂₁ t₁₁ t₂₁}
        {From₁ : Setoid f₁₁ f₂₁} {To₁ : Setoid t₁₁ t₂₁}
        {f₁₂ f₂₂ t₁₂ t₂₂}
        {From₂ : Setoid f₁₂ f₂₂} {To₂ : Setoid t₁₂ t₂₂}
        {f₁ f₂ t₁ t₂} {From : Setoid f₁ f₂} {To : Setoid t₁ t₂} →
      ((From₁ ⟶ To₁) → (From₂ ⟶ To₂) → (From ⟶ To)) →
      ((To₁ ⟶ From₁) → (To₂ ⟶ From₂) → (To ⟶ From)) →
      Equivalence From₁ To₁ → Equivalence From₂ To₂ →
      Equivalence From To
zip t f eq₁ eq₂ =
  record { to = t (to eq₁) (to eq₂); from = f (from eq₁) (from eq₂) }
  where open Equivalence

------------------------------------------------------------------------
-- Equivalence is an equivalence relation

-- Identity and composition (reflexivity and transitivity).

id : ∀ {s₁ s₂} → Reflexive (Equivalence {s₁} {s₂})
id {x = S} = record
  { to   = F.id
  ; from = F.id
  }

infixr 9 _∘_

_∘_ : ∀ {f₁ f₂ m₁ m₂ t₁ t₂} →
      TransFlip (Equivalence {f₁} {f₂} {m₁} {m₂})
                (Equivalence {m₁} {m₂} {t₁} {t₂})
                (Equivalence {f₁} {f₂} {t₁} {t₂})
f ∘ g = record
  { to   = to   f ⟪∘⟫ to   g
  ; from = from g ⟪∘⟫ from f
  } where open Equivalence

-- Symmetry.

sym : ∀ {f₁ f₂ t₁ t₂} →
      Sym (Equivalence {f₁} {f₂} {t₁} {t₂})
          (Equivalence {t₁} {t₂} {f₁} {f₂})
sym eq = record
  { from       = to
  ; to         = from
  } where open Equivalence eq

-- For fixed universe levels we can construct setoids.

setoid : (s₁ s₂ : Level) → Setoid (suc (s₁ ⊔ s₂)) (s₁ ⊔ s₂)
setoid s₁ s₂ = record
  { Carrier       = Setoid s₁ s₂
  ; _≈_           = Equivalence
  ; isEquivalence = record {refl = id; sym = sym; trans = flip _∘_}
  }

⇔-setoid : (ℓ : Level) → Setoid (suc ℓ) ℓ
⇔-setoid ℓ = record
  { Carrier       = Set ℓ
  ; _≈_           = _⇔_
  ; isEquivalence = record {refl = id; sym = sym; trans = flip _∘_}
  }
