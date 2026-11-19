-- The type of `x` singles out `C.c`, whose result type differs from `El i`
-- for every index `i`.  Trying inversion first would select `A.c` and give
-- an error at `x`.  Disambiguation by argument type must take precedence to
-- preserve the error about the result type of `C.c`.

module ConstructorDisambiguationByInversion-ArgsFirst where

open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤)

data A : Set where
  c : Nat → A

data C : Set where
  c : ⊤ → C

El : Bool → Set
El false = A
El true  = Bool

index : ∀ {i} → El i → Bool
index {i} _ = i

test : ⊤ → Bool
test x = index (c x)  -- Agda should select `C.c` and report its incompatible result type.
