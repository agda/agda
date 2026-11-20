-- Both meanings of `c` have a target returned by `El`.  Choosing `A.c`
-- would give the index `false`, and choosing `B.c` would give `true`.
-- There is no further constraint on the index, so Agda must leave `c` ambiguous.

module ConstructorDisambiguationByInversion-Ambiguous where

open import Agda.Builtin.Bool using (Bool ; false ; true)

data A : Set where
  c : A

data B : Set where
  c : B

El : Bool → Set
El false = A
El true  = B

index : ∀ {i} → El i → Bool
index {i} _ = i

ambiguous : Bool
ambiguous = index c  -- Both `A.c` and `B.c` are possible.
