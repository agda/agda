-- Two different constructors of `D` are in scope under the name `c`.
-- Both choices give the same index `false`.  Even though there is only
-- one possible datatype for `c`, Agda must retain both constructor candidates.

module ConstructorDisambiguationByInversion-AmbiguousRenamed where

open import Agda.Builtin.Bool using (Bool ; false ; true)

data D : Set where
  a : D
  b : D

open D renaming (a to c)
open D renaming (b to c)

El : Bool → Set
El false = D
El true  = Bool

index : ∀ {i} → El i → Bool
index {i} _ = i

test : Bool
test = index c  -- Both `D.a` and `D.b` are possible.
