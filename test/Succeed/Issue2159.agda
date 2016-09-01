
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data AB : Set where
  A B : AB

foo : Nat → AB → AB
foo 0       t = A
foo (suc n) t = foo n A -- NB tail-recursive

test : foo 100000 A ≡ A
test = refl -- memory blows up here

data N : Set where
  z : N
  s : N → N

produce : Nat → AB → N
produce 0       t = z
produce (suc n) t = s (produce n A)

consume : N → AB → AB
consume z     t = t
consume (s n) t = consume n A

test₁ : consume (produce 100000 B) A ≡ A
test₁ = refl
