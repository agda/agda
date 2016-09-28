
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

pathological : (e : 9999999999 ≡ 9999999999) → Set
pathological refl = Nat
