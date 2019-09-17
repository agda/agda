open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- _ can only be used to separate groups of 3
_ : 100_00 * 100_000 ≡ 1_000_000_000
_ = refl
