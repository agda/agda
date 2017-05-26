
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

data D : Set where
  c₁ : ⊥ → D
  c₂ : D

Parses : D → Set₁
Parses = λ where
  c₂      → Set
  (c₁ ())

Does-not-parse : D → Set₁
Does-not-parse = λ where
  (c₁ ())
  c₂      → Set
