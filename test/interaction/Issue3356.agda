-- 2018-11-02, Jesper:
-- Problem reported by Martin Escardo
-- Example by Guillaume Brunerie
-- C-c C-s was generating postfix projections
-- even with --postfix-projections disabled.

open import Agda.Builtin.Equality

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

postulate
  A B : Set
  p : A × B

eta : p ≡ ({!!} , snd p)
eta = refl

-- C-c C-s should fill the hole with 'fst p'.
