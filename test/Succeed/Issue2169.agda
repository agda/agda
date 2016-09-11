
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Float

foo : primFloatEquality 0.0 -0.0 ≡ false
foo = refl
