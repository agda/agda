-- Andreas, 2026-08-26, issue #8686
-- Report and test case by @bdrisc-ant, attributed to Claude.
-- False with projection-like function where the principal argument
-- is of a data type with an irrelevant parameter.

{-# OPTIONS --safe --projection-like #-}

-- A function whose principal argument has a data type with an
-- IRRELEVANT parameter is recognised as projection-like, and the
-- parameter is dropped from its applications.  But the type of the
-- principal argument does not determine an irrelevant parameter
-- (D ⊤ and D Bool are definitionally equal), so the conversion
-- checker reconstructs the wrong parameter and compares the remaining
-- arguments at the wrong type.  Result: a closed proof of true ≡ false.
--
-- Expected: 'lemma' is rejected (a != b of type Bool), as it is with
-- --no-projection-like.

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record ⊤ : Set where

data D .(A : Set) : Set where
  c₁ c₂ : D A

-- Projection-like in its argument of type D A; the hidden A is dropped.
-- (The λ right-hand sides only serve to keep 'select' out of the
-- injectivity analysis, which would otherwise exclude it from
-- projection-likeness.)
select : {A : Set} → D A → A → A → A
select c₁ a = λ _ → a
select c₂ _ = λ b → b

-- x : D ⊤ is accepted at type D Bool because the parameter is irrelevant.
-- The stuck applications 'select x a' and 'select x b' are then compared
-- with their arguments typed from x's type D ⊤, i.e. a = b : ⊤, which
-- holds by η for the unit record although a b : Bool.
lemma : (x : D ⊤) (a b : Bool) → select {Bool} x a ≡ select {Bool} x b
lemma x a b = refl

app : {g h : Bool → Bool} → g ≡ h → g true ≡ h true
app refl = refl

boom : true ≡ false
boom = app (lemma c₁ true false)

-- Expected error: [UnequalTerms]
-- The terms
--   a
-- and
--   b
-- are not equal at type Bool
-- when checking that the expression refl has type
-- select x a ≡ select x b
