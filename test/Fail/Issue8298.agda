-- Reported by Shu-Hung You

open import Agda.Builtin.Sigma

test : (A : Set) → A → Σ A (λ _ → A)
test A x =
  let
    pr : Σ A (λ _ → A)
    fst pr = x
  in pr
