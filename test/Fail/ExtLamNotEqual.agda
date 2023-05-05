module ExtLamNotEqual where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

f g : Nat → Nat
f = λ { zero → zero ; (suc n) → suc n }
g = λ { zero → zero ; (suc n) → suc n }

_ : f ≡ g
_ = refl
