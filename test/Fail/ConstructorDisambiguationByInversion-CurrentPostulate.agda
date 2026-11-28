-- Constructor disambiguation uses a postulated result head only outside its
-- declaring mutual block.  This restriction applies here even though `P`
-- remains a postulate.  The result head arises from supplying `P` to `El`.

module ConstructorDisambiguationByInversion-CurrentPostulate where

open import Agda.Builtin.Bool using (Bool ; false ; true)

data A : Set where
  c : A

data B : Set where
  c : B

El : Set → Bool → Set
El X false = A
El X true  = X

index : (X : Set) → ∀ {i} → El X i → Bool
index X {i} _ = i

mutual
  postulate P : Set

  ambiguous : Bool
  ambiguous = index P c  -- The choice between `A.c` and `B.c` is postponed.
