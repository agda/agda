
module tmp where

open import univ
open import cwf
open import Base
open import Nat
open import help
open import proofs

{- TODO: Prove

  (Π A B) / σ = Π (A / σ) (B / (σ / wk ,, vz))

  (λ v) ∙ u = v // [ u ]    (β)
  w = λ ((w // wk) ∙ vz)    (η)

  λ v // σ = λ (v // (σ ∘ wk ,, vz))
  w ∙ u // σ = (w // σ) ∙ (u // σ)


-}

