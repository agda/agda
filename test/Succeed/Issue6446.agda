open import Agda.Primitive

Seti : (ℓ : Level) → Set (lsuc ℓ)
Seti ℓ = Set ℓ

lvl0 : Set → Level
lvl0 _ = lzero

ty : Set₁
ty = (X : Set) → Seti (lvl0 X)
