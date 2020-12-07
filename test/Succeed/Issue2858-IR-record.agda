open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

interleaved mutual

  data Rec : Set
  ⟦_⟧ : Rec → Set

  constructor `Nat : Rec
  ⟦ `Nat   ⟧ = Nat

  _ : Rec
  _ = `Σ `Nat (λ _ → `Nat)

  _ : Rec → Rec
  _ = λ r → `Σ r (λ _ → `Nat)

  constructor `Σ : (r : Rec) → (⟦ r ⟧ → Rec) → Rec
  ⟦ `Σ A B ⟧ = Σ ⟦ A ⟧ λ a → ⟦ B a ⟧

_+1-Nats : Nat → Rec
zero  +1-Nats = `Nat
suc n +1-Nats = `Σ `Nat λ _ → n +1-Nats

Nats : Rec
Nats = `Σ `Nat _+1-Nats

[1] : ⟦ Nats ⟧
[1] = 0 , 1

[1⋯3] : ⟦ Nats ⟧
[1⋯3] = 2 , 1 , 2 , 3
