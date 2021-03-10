open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

postulate
  F    : Set → Set₁
  P    : (A : Set) → F A → Set
  easy : {A : Set₁} → A

A : Set₁
A = Σ Set λ B → Σ (F B) (P B)

f : (X Y : A) → X ≡ Y
f (C , x , p) (D , y , q) = proof
  module _ where
  abstract

    proof : (C , x , p) ≡ (D , y , q)
    proof = easy
