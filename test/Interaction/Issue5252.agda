open import Agda.Primitive
open import Agda.Builtin.Sigma

data Empty : Set where

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Set (ℓ ⊔ ℓ')
A ≃ B = Σ (A → B) λ f → Empty

record Iso {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') : Set (ℓ ⊔ ℓ') where
  field
    inv : B → A

postulate
  isoToEquiv : ∀{ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → Iso A B → A ≃ B

works : Iso (∀ {a : Set} → a) Empty
works = λ where
  .Iso.inv n → {!n!}

-- something like  (∀ {A : Set} → A)  seems to be necessary to trigger

test : (∀ {A : Set} → A) ≃ Empty
test = isoToEquiv λ where
  .Iso.inv n → {!n!}
