
open import Agda.Builtin.String
open import Agda.Builtin.Equality

test : String → String → String
test "x" b = "left"
test a "x" = "right"
test a b = "nowhere"

_ : test "a" "x" ≡ "right"
_ = refl
