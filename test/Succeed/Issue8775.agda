-- Andreas, 2026-09-24, issue #8775, regression introduced by #8497.
--
-- The occurs check refused to solve
--
--   _A := ♭ ((u : ♭ A) → fam u)
--
-- because the locally bound variable @u@, which has the default (continuous)
-- cohesion, was checked against the ambient modality of the position it occurs
-- in, which is @♭ since it is inside the crisp argument of ♭.
-- However, variables bound underneath a crisp position are themselves crisp.
--
-- Shrunk from agda-unimath, modal-type-theory.crisp-dependent-function-types.

{-# OPTIONS --cohesion --flat-split #-}

module Issue8775 where

data ♭ (@♭ A : Set) : Set where
  con : @♭ A → ♭ A

id : {A : Set} → A → A
id x = x

module _ {@♭ A : Set} {@♭ B : @♭ A → Set} where

  fam : ♭ A → Set
  fam (con x) = B x

  postulate
    f : ♭ ((u : ♭ A) → fam u)

  -- Solving the implicit argument of @id@ goes through the occurs check.
  test : ♭ ((u : ♭ A) → fam u)
  test = id f
