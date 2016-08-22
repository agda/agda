
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data ⊤ : Set where
  tt : ⊤

foo : Nat → ⊤ → ⊤
foo 0 tt = tt
foo (suc n) tt = foo n tt -- NB tail-recursive

test : foo 100000 tt ≡ tt
test = refl -- memory blows up here
