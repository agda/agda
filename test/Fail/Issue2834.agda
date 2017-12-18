open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

test : (A : Set) (let X = _) (x : X) (p : A ≡ Bool) → Bool
test .Bool true  refl = false
test .Bool false refl = true
