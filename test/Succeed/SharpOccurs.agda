{-# OPTIONS --cohesion --allow-unsolved-metas #-}
module SharpOccurs where

open import Agda.Builtin.Equality

data Sharp (@♯ A : Set) : Set where
  con : (@♯ x : A) → Sharp A

-- Non-interactive reconstruction of giving {! con _ !} for the body of unit
--
-- should have exactly one unsolved meta (the argument to con in the type signature of blah)
-- because the occurs checker should know that the variables
--   {A : Set} {x : A}
-- become flat (and so can be used in a flat context) when going under
-- the sharp argument of con, even though the body of _ is in a
-- continuous context

unit : {A : Set} → A → Sharp A
blah : ∀ {A} {x : A} → unit x ≡ Sharp.con _

unit x = _
blah = refl
