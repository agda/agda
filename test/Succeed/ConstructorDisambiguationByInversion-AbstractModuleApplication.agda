-- Referring to an abstract datatype through a module application can still give its
-- original name in the inversion map.  When the copy unfolds to the original,
-- Agda can use the visible datatype name to exclude it as a result type for both constructors.

module ConstructorDisambiguationByInversion-AbstractModuleApplication where

open import Agda.Builtin.Bool using (Bool ; false ; true)

module Family (b : Bool) where
  abstract
    data D : Set where
      d : D

module Copy = Family true using (D)

data A : Set where
  c : A

data B : Set where
  c : B

-- Outside the abstract block, the instantiated type is visible but its constructor is hidden.
-- The second clause refers to that type through the module application.
El : Bool → Set
El false = A
El true  = Copy.D

index : ∀ {i} → El i → Bool
index {i} _ = i

test : Bool
test = index c  -- Only `A.c` has a result type returned by `El`.
