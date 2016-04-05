
module _ where

open import Agda.Builtin.Nat
open import Imports.ImportedDisplayForms

postulate
  T : Nat → Set

foo : (a : Nat) → T (a + a)
foo a = {!!}
