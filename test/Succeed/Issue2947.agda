
open import Agda.Builtin.Nat

[_] :  (Nat → Set) → Set
[ T ] = ∀ {i} → T i

data D : Nat → Nat → Set where
  c : ∀ {i} → [ D i ]
