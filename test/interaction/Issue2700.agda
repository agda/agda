open import Agda.Builtin.Nat

record Pointed (A : Set) : Set where
 field point : A

it : ∀ {A : Set} {{x : A}} → A
it {{x}} = x

instance _ = record { point = 3 - 4 }

_ : Pointed Nat
_ = {!!}
