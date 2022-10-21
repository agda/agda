{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive            renaming (Set to Type)
open import Agda.Primitive.Cubical    renaming (primComp to comp)
open import Agda.Builtin.Sigma
open import Agda.Builtin.Cubical.Sub  renaming (primSubOut to outS)
open import Agda.Builtin.Cubical.Glue using    (primGlue; _≃_)

Glue : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
       → (Te : Partial φ (Σ (Type ℓ') (_≃ A)))
       → Type ℓ'
Glue A Te = primGlue A (λ x → Te x .fst) (λ x → Te x .snd)

compGlue :
  {ℓ ℓ' : Level}
  (Y    : I → Type ℓ')
  (φ    : I → I)
  (Te   : (i : I) → Partial (φ i) (Σ (Type ℓ) (_≃ Y i)))
  (ψ    : I)
  (x    : (i : I) → Partial ψ (Glue (Y i) (Te i)))
  → Sub (Glue (Y i0) (Te i0)) ψ (x i0)
  → Sub (Glue (Y i1) (Te i1)) ψ (x i1)

compGlue Y φ Te ψ x x₀ = inS (comp (λ i → Glue (Y i) (Te i)) x (outS x₀))
