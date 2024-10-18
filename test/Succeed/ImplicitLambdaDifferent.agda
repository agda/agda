module ImplicitLambdaDifferent where

open import Agda.Builtin.Nat

_ =
  let
    test : {A B : Set} {C : Nat} → Nat
    test = λ {C = C} → C
  in test {Nat} {Nat} {123}
