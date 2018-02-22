
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.TrustMe

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _×_

-- Nested pattern prevents record pattern translation.
f : Nat × Nat → Nat
f (zero  , b) = b
f (suc a , b) = a + b

-- With catch-all case
g : Nat × Nat → Nat
g (zero , b) = b
g p          = fst p + snd p

-- Definition by copatterns.
p : Nat × Nat
p .fst = 2
p .snd = 2

test-f : f p ≡ 3
test-f = refl

test-g : g p ≡ 4
test-g = refl

-- Slow reduce. primTrustMe doesn't use fast-reduce

is-refl : ∀ {A : Set} (x y : A) → x ≡ y → Bool
is-refl x y refl = true

test-slow-f : is-refl (f p) 3 primTrustMe ≡ true
test-slow-f = refl

test-slow-g : is-refl (g p) 4 primTrustMe ≡ true
test-slow-g = refl
