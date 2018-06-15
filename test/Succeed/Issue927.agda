{-# OPTIONS --irrelevant-projections #-}

-- Andreas, 2013-10-29 submitted by sanzhiyan
-- Documents need for different treating of DontCare in
-- linearity analysis of Miller unification.
-- Now, there can be DontCares stemming from irrelevant projections.

module Issue927 where

import Common.Level

module Fails where

  postulate
    Σ : (B : Set) (C : B → Set) → Set

    <_,_> : {A : Set} {B : A → Set} {C : ∀ x → B x → Set}
          (f : (x : A) → B x) →
          (g : (x : A) → C x (f x)) →
          ((x : A) → Σ (B x) (C x))

  record _⟶_ (A B : Set) : Set  where
    field
      .app : A → B

  open _⟶_ public

  .⟪_,_⟫ : ∀ (A B C : Set) → (A ⟶ B) → (A ⟶ C) → A → Σ B (\ _ → C)
  ⟪_,_⟫ A B C f₁ f₂ = < app f₁ , app f₂ >

-- WAS:
-- Using darcs Agda, the following code triggers an
-- internal error at src/full/Agda/TypeChecking/MetaVars.hs:897
