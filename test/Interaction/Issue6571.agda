module Issue6571 where

open import Agda.Builtin.Nat

idf : (∀ {A : Set} → A → A) → Nat
idf f = f 0

_ : Nat → Nat
_ = λ x → {! idf λ _ → ? !}
