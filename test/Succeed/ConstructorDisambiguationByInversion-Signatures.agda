-- A blocked type family may return a data or record type whose declaration is incomplete
-- or abstract.  Its name can still distinguish it from the parents of overloaded constructors.

module ConstructorDisambiguationByInversion-Signatures where

open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.List using ([] ; _∷_)
open import Agda.Builtin.Reflection using (TC ; returnTC ; typeError ; strErr)
open import Agda.Builtin.Unit using (⊤ ; tt)

data A : Set where
  c : A

data B : Set where
  c : B

El : Set → Bool → Set
El X false = A
El X true  = X

index : ∀ {i} (X : Set) → El X i → Bool
index {i} X _ = i

-- Inspect the inferred index while the data or record signature is still incomplete.
-- Checking an ordinary definition can be postponed until the datatype or record is complete.
-- Pattern matching here observes the value already inferred by Agda without constraining it.
checkFalse : Bool → TC ⊤
checkFalse false = returnTC tt
checkFalse true  = typeError (strErr "Expected the index false" ∷ [])

-- While checking the splice, Agda has only the signature of `D`.  Its name already
-- distinguishes it from both constructor parents, so the index can be inferred immediately.
module ForwardData where
  mutual
    data D : Set

    unquoteDecl = checkFalse (index D c)  -- Only `A.c` has a result type returned by `El D`.

    data D where
      d : D

-- A forward record signature has its own name before its fields have been checked.
-- Using that name should suffice to distinguish `R` from the parents of both constructors.
module ForwardRecord where
  mutual
    record R : Set

    unquoteDecl = checkFalse (index R c)  -- Only `A.c` has a result type returned by `El R`.

    record R where
      field value : Bool

-- Outside the abstract block, Agda can distinguish `D` from `A` and `B` by its name.
-- This suffices to select a public constructor even though the constructors of `D` are hidden.
module AbstractData where
  abstract
    data D : Set where
      d : D

  inferredIndex : Bool
  inferredIndex = index D c  -- Of the public constructors, only `A.c` fits.

-- Outside the abstract block, the record constructor is unavailable.  The declared name
-- of `R` still suffices to rule out that branch without inspecting the fields.
module AbstractRecord where
  abstract
    record R : Set where
      constructor r
      field value : Bool

  inferredIndex : Bool
  inferredIndex = index R c  -- Of the public constructors, only `A.c` fits.
