
open import Agda.Builtin.Nat
open import Agda.Builtin.Unit

data ⊥ : Set where

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

Fin : Nat → Set
Fin zero    = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

n = 49

postulate
  P : Nat → Set
  Q : Set → Set
  f : (n : Nat) → Q (Fin n) → P n
  q : Q (Fin n)

p : P n
p = f _ q
