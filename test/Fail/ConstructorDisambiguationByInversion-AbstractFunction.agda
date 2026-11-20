-- The second result of `El` is supplied at the call site.  Here the argument
-- is an abstract function whose body defines it to be `B`.  Treating its
-- name as a distinct datatype would select `A.c` from the first clause.

module ConstructorDisambiguationByInversion-AbstractFunction where

open import Agda.Builtin.Bool using (Bool ; false ; true)

data A : Set where
  c : A

data B : Set where
  c : B

abstract
  X : Set
  X = B

El : Set → Bool → Set
El T false = A
El T true  = T

index : (T : Set) → ∀ {i} → El T i → Bool
index T {i} _ = i

test : Bool
test = index X c  -- The choice between `A.c` and `B.c` must remain open.
