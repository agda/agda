-- A module with a solved interaction point.

module Issue1296.SolvedMeta where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

test : zero ≡ {!!}
test = refl
