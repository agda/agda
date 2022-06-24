open import Agda.Primitive

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

foldWrap : {A B : Set} → (A → B) → Wrap A → B
foldWrap f (wrap x) = f x

id₀ : Level → Level
id₀ ℓ = ℓ

id₁ : Level → Level
id₁ = id₀

id₂ : {wℓ : Wrap Level}
    → Set (foldWrap id₀ wℓ ⊔ foldWrap id₁ wℓ)
    → Set (foldWrap id₀ wℓ)
id₂ A = A
