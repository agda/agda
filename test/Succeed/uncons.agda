open import Agda.Builtin.Maybe
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

_ : primStringUncons "abcd" ≡ just ('a', "bcd")
_ = refl
