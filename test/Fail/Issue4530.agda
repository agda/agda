
open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat public

data IsTrue : Bool → Set where
  instance truth : IsTrue true

postulate
  foo : {{IsTrue (3 < 2)}} → Nat

test : Nat
test = foo
