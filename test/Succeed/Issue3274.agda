
open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where

variable
  A  : Set
  x  : A
  n  : Nat
  xs : Vec A n

postulate
  IsHead : A → Vec A (suc n) → Set

-- The `n` should be generalized over since the generalizable n in the type of xs
-- is solved with suc n.
foo : IsHead {n = _} x xs → Nat
foo h = 0

check-foo : {A : Set} {x : A} {n : Nat} {xs : Vec A (suc n)} → IsHead x xs → Nat
check-foo = foo

-- Should work also if the meta is created in an extended context
bar : (X : Set) → IsHead x xs → Nat
bar X h = 0

check-bar : {A : Set} {x : A} {n : Nat} {xs : Vec A (suc n)} → (X : Set) → IsHead x xs → Nat
check-bar = bar
