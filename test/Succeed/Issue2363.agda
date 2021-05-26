{-# OPTIONS --guardedness #-}

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
        n : Nat

data P (r : R) : Nat → Set where
  fTrue  : R.f r ≡ true → P r zero
  nSuc   : P r (suc (R.n r))

data Q : (b : Bool) (n : Nat) →  Set where
  true! : Q true zero
  suc!  : ∀{b n} → Q b (suc n)

test : (r : R) {n : Nat} (p : P r n) → Q (R.f r) n
test r nSuc       = suc!
test r (fTrue p)  with R.f r
test _ (fTrue ()) | false
test _ _          | true = true!  -- underscore instead of (isTrue _)

-- -- Note that `with` first and then splitting on p does not work:
--
-- foo :  (r : R) {n : Nat} (p : P r n) → Q (R.f r) n
-- foo r p with R.f r
-- foo r (fTrue x) | false = {!x!}  -- cannot split on x
-- foo r (fTrue _) | true  = true!
-- foo r nSuc      | _     = suc!
