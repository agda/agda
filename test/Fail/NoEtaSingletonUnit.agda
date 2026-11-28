module NoEtaSingletonUnit where

open import Agda.Builtin.Unit
open import Agda.Builtin.Equality

test : (x y : ⊤) → x ≡ y
test x y = refl
