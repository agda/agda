-- Andreas, 2026-09-25, exploiting a call to `canonicalName`.
-- Exploit constructed by Claude, triggering an internal error.

-- Same as Issue8777.agda, but for a record type copy,
-- exercising the `Record` branch of `disambiguateConstructor`.

module Issue8777a where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool

postulate P Q : Set

module M (A : Set) where
  record R : Set where
    constructor mk

-- N.R has TWO parameters, while M.mk : {A : Set} → M.R A has only ONE Pi.
module N (Y1 Y2 : Set) = M Y1

macro
  go : Term → TC ⊤
  go hole =
    bindTC (quoteTC (N.R P Q → Set)) λ ty →
    -- Keep N.R from unfolding, so the split type stays headed by the copy.
    withReduceDefs (false , (quote N.R ∷ []))
      (bindTC (checkFromStringTC "λ { N.mk → P }" ty) (unify hole))

test : N.R P Q → Set
test = go

-- Current error: [ConstructorPatternInWrongDatatype]
-- N.mk is not a constructor of the datatype N.R
-- when checking that the pattern N.mk has type N.R P Q
