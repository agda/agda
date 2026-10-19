
open import Agda.Builtin.Bool

record R : Set where
  field
    f : Bool

f : R → Bool
f x = {!x!}
