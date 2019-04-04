
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

record Monad (M : Set → Set) : Set₁ where
  field
    return : {A : Set} → A → M A
    _>>=_  : {A B : Set} → M A → (A → M B) → M B

open Monad ⦃ … ⦄

postulate
  F G : Set → Set

instance

  postulate
    G-monad : Monad G
    F-monad : Monad F

f : Σ Nat (λ _ → Nat) → F Nat
f p = do
  m , n ← return p
  return (m n)

-- Should jump to `m n` and list the F-monad candidate error first.
