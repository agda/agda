open import Agda.Builtin.Bool
open import Agda.Builtin.Char
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

char : Char → Set
char 'A' with 'O'
char _ | _ = Char
char _ = Char

lit : Nat → Set
lit 5 with 0
lit _ | _ = Nat
lit _ = Nat

con : Nat → Set
con zero    with zero
con _       | _ = Nat
con (suc x) with zero
con _       | _ = Nat

record R : Set where
  coinductive -- disallow matching
  field f : Bool

data P (r : R) : Set where
  isTrue : R.f r ≡ true → P r

data True : (b : Bool) →  Set where
  true! : True true

test : (r : R) (p : P r) → True (R.f r)
test r (isTrue p) with R.f r
test _ _           | true = true!  -- underscore instead of (isTrue _)
test _ (isTrue ()) | false
