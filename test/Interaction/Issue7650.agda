open import Agda.Builtin.Equality
open import Agda.Builtin.Bool

test : Bool
test with true in eq
... | x = {!eq!}
