-- Recognizing the abstract datatype returned by a type family must respect constructor visibility.
-- Outside its abstract block the only constructor of `D` is unavailable.

module ConstructorDisambiguationByInversion-HiddenConstructor where

open import Agda.Builtin.Bool using (Bool ; false ; true)

data A : Set where
  c : A

data B : Set where
  c : B

abstract
  data D : Set where
    c : D

El : Bool → Set
El false = D
El true  = Bool

index : ∀ {i} → El i → Bool
index {i} _ = i

-- The public constructors belong to neither possible result type.  Considering the hidden
-- constructor as a candidate would expose `D.c` through the overloaded name.
test : Bool
test = index c  -- The choice must remain unresolved after `D.c` is excluded.
