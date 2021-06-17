
module _ where

open import Agda.Builtin.Bool

postulate Eq : Set → Set

it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

module M1 (A : Set) ⦃ eqA : Eq A ⦄ where
  postulate B : Set
  variable  n : B
  postulate P : B → Set

module M2 (A : Set) ⦃ eqA : Eq A ⦄ where
  open M1 A
  postulate
    p₁ : P n
    p₂ : P ⦃ it ⦄ n
    p₃ : P ⦃ eqA ⦄ n
    p₄ : M1.P A n
