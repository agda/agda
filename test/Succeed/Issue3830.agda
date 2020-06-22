open import Agda.Builtin.String
open import Agda.Builtin.Equality

_ : primShowChar 'c' ≡ "'c'"
_ = refl

_ : primShowString "ccc" ≡ "\"ccc\""
_ = refl

