
open import Agda.Builtin.Nat
open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit

macro
  five : Term → TC ⊤
  five hole = unify hole (lit (nat 5))

-- Here you get hole = _X (λ {n} → y {_n})
-- and fail to solve _n.
yellow : ({n : Nat} → Set) → Nat
yellow y = five

-- Here you get hole = _X ⦃ n ⦄ (λ ⦃ n' ⦄ → y ⦃ _n ⦄)
-- and fail to solve _n due to the multiple candidates n and n'.
more-yellow : ⦃ n : Nat ⦄ → (⦃ n : Nat ⦄ → Set) → Nat
more-yellow y = five
