-- Andreas, 2026-09-25, exploiting a call to `canonicalName`.
-- Exploit constructed by Claude, triggering an internal error.

module Issue8777 where

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Sigma
open import Agda.Builtin.Bool

postulate P Q : Set

module M (A : Set) where
  data D : Set where
    c : D

-- N.D has TWO parameters, while M.c : {A : Set} → M.D A has only ONE Pi.
module N (Y1 Y2 : Set) = M Y1

macro
  go : Term → TC ⊤
  go hole =
    bindTC (quoteTC (N.D P Q → Set)) λ ty →
    -- Keep N.D from unfolding, so the split type stays headed by the copy.
    withReduceDefs (false , (quote N.D ∷ []))
      (bindTC (checkFromStringTC "λ { N.c → P }" ty) (unify hole))

test : N.D P Q → Set
test = go

-- Current error: [ConstructorPatternInWrongDatatype]
-- N.c is not a constructor of the datatype N.D
-- when checking that the pattern N.c has type N.D P Q
