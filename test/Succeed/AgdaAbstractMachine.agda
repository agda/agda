-- Some tests for the Agda Abstract Machine.

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

_×_ : Set → Set → Set
A × B = Σ A λ _ → B

id : Nat → Nat
id x = x

-- Applying id should not break sharing
double : Nat → Nat
double n = id n + id n

pow : Nat → Nat
pow zero    = 1
pow (suc n) = double (pow n)

test-pow : pow 64 ≡ 18446744073709551616
test-pow = refl

-- Projections should not break sharing
addPair : Nat × Nat → Nat
addPair p = fst p + snd p

dup : Nat → Nat × Nat
dup x .fst = x
dup x .snd = x

smush : Nat × Nat → Nat × Nat
smush p = dup (addPair p)

iter : {A : Set} → (A → A) → Nat → A → A
iter f zero    x = x
iter f (suc n) x = f (iter f n x)

pow' : Nat → Nat
pow' n = addPair (iter smush n (0 , 1))

test-pow' : pow' 64 ≡ pow 64
test-pow' = refl

-- Should not be linear (not quadratic) for neutral n.
builtin : Nat → Nat → Nat
builtin k n = k + n - k

test-builtin : ∀ n → builtin 50000 n ≡ n
test-builtin n = refl
