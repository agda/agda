
data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim = λ where ()

⊥-elim₂ : {A : Set} → ⊥ → A → A
⊥-elim₂ = λ where () _

⊥-elim₃ : {A : Set} → A → ⊥ → A
⊥-elim₃ = λ where _ ()
