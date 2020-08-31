open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

_ : 10_000 * 100_000 ≡ 1_000_000_000
_ = refl

_ : 0xDEADBEEF ≡ 3735928559
_ = refl

_ : 0b01001000_01001001 ≡ 18505
_ = refl
