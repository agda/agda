
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

foo : Nat → (Nat → Nat) → Nat
foo zero    f = f zero
foo (suc n) f = foo n λ n → f (suc n)

fsuc : (Nat → Nat) → Nat → Nat
fsuc f n = f (suc n)

foo' : Nat → (Nat → Nat) → Nat
foo' zero    f = f zero
foo' (suc n) f = foo' n (fsuc f)

foo'' : Nat → (Nat → Nat) → Nat
foo'' zero    f = f zero
foo'' (suc n) f = foo'' n λ { n → f (suc n) }

test : foo 50000 (λ n → n) ≡ 50000
test = refl

test' : foo' 50000 (λ n → n) ≡ 50000
test' = refl

test'' : foo'' 50000 (λ n → n) ≡ 50000
test'' = refl
