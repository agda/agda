module InstanceExpensiveContext where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

ack : Nat → Nat → Nat
ack zero    n       = suc n
ack (suc m) zero    = ack m 1
ack (suc m) (suc n) = ack m (ack (suc m) n)

force-nat : Nat → Set
force-nat zero    = ⊤
force-nat (suc x) = force-nat x

auto : {A : Set} ⦃ _ : A ⦄ → A
auto ⦃ x ⦄ = x

postulate
  T : Set
  instance x : T

-- tests that instance search doesn't go into a tailspin if the context
-- contains variables whose type is difficult to reduce

t1 : force-nat (ack 4 4) → T
t1 _ = auto

t2 : (⊤ → force-nat (ack 4 4)) → T
t2 _ = auto
