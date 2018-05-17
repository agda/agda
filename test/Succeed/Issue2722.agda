{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical

postulate
  A : Set
  B : Set
  b : B

postulate
  PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ

{-# BUILTIN PATHP        PathP     #-}

infix 4 _≡_
_≡_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} = PathP (λ _ → A)

f : (\ {a : A} (x : B) → b) ≡ (\ _ → b)
f i x = b
