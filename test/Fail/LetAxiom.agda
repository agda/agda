module LetAxiom where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

test : Nat
test =
  let
    x : Nat
  in x

-- Was: not a valid let binding
-- Should be: missing definition, but type checking proceeds

_ : 2 + 2 ≡ 4
_ = refl
