
open import Agda.Primitive

postulate
  ℓ : Level
  F : Level → Set

module Two where

  mutual

    α : Level
    α = _

    G : F (α ⊔ ℓ) → F ℓ
    G A = A

    H : F (α ⊔ ℓ) → F α
    H A = A

module Three where

  mutual

    α : Level
    α = _

    β : Level
    β = _

    G : F (α ⊔ β ⊔ ℓ) → F ℓ
    G A = A

    H : F (α ⊔ β ⊔ ℓ) → F α
    H A = A

    I : F (α ⊔ β ⊔ ℓ) → F β
    I A = A
