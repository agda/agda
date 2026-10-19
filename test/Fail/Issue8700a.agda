{-# OPTIONS --safe --without-K #-}

-- Issue found by Claude and reported by bdrisc-ant on Github

-- While the clauses of a function are being checked, the function reduces
-- via the clauses checked so far.  A call that is stuck because the
-- remaining clauses are still missing is treated by the clause matcher as a
-- *definite* mismatch against a constructor pattern, so an enclosing call
-- reduces by a later clause to a value that the completed definition
-- contradicts.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data ⊥ : Set where

f : Bool → Bool → Bool
f true  true  = false
f x     true  = true
f false false = true
  module M where
    -- Checked when only the first two clauses of f are in the signature.
    -- The inner call  f false false  is stuck (no clause yet); the matcher
    -- reports a definite mismatch against the pattern  true  of the first
    -- clause, and the outer call reduces by the second clause to  true.
    lem : f (f false false) true ≡ true
    lem = refl
f true  false = false

-- Once f is complete,  f (f false false) true = f true true = false.

discr : false ≡ true → ⊥
discr ()

boom : ⊥
boom = discr M.lem
