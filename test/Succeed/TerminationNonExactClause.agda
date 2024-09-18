open import Agda.Builtin.Bool

f : Bool → Bool
f false = f true
f _ = true
