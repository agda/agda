-- Andreas, 2026-08-26, issue #8686
-- Report and test case by @bdrisc-ant, attributed to Claude.
-- False with projection-like function where the principal argument
-- is of a data type with a phantom argument that reduces away.

{-# OPTIONS --safe --projection-like #-}

-- A data type COPIED by a module application reduces to an instance of
-- the original: here N.D B reduces to M.D ⊤ for every B, so the type
-- N.D B does not determine B.  A function whose principal argument has
-- type N.D B must therefore not become projection-like (dropping B):
-- otherwise B is "reconstructed" from the reduct M.D ⊤ of the principal
-- argument's type -- i.e. taken to be M's argument ⊤ -- and the
-- remaining arguments are compared at ⊤ instead of Bool.
-- No irrelevance is involved, and x has exactly the expected type.
--
-- Expected: 'lemma' is rejected (a != b of type Bool), as it is with
-- --no-projection-like.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record ⊤ : Set where

module M (A : Set) where
  data D : Set where
    c₁ c₂ : D

module N (B : Set) = M ⊤

select : {B : Set} → N.D B → B → B → B
select N.c₁ a = λ _ → a
select N.c₂ _ = λ b → b

lemma : (x : N.D Bool) (a b : Bool) → select x a ≡ select x b
lemma x a b = refl

app : {g h : Bool → Bool} → g ≡ h → g true ≡ h true
app refl = refl

boom : true ≡ false
boom = app (lemma (N.c₁ {Bool}) true false)

-- Expected error: [UnequalTerms]
-- The terms
--   a
-- and
--   b
-- are not equal at type Bool
-- when checking that the expression refl has type
-- select x a ≡ select x b
