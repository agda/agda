-- Andreas, 2016-10-03, re issue #2231
-- Termination checking a corecursive definition in abstract mode.

{-# OPTIONS --guardedness #-}

infix 1000 ♯_

postulate
  ∞  : ∀ {a} (A : Set a) → Set a
  ♯_ : ∀ {a} {A : Set a} → A → ∞ A
  ♭  : ∀ {a} {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

abstract
  data Functor : Set where
    Id : Functor

  _·_ : Functor → Set → Set
  Id · A = A

  data ν (F : Functor) : Set where
    inn : ∞ (F · ν F) → ν F

  -- Evaluation is required to see that Id · ν Id is a coinductive type.

  foo : ∀ F → F · ν F
  foo Id = inn (♯ foo Id)

-- The termination checker needs to treat the generated #-foo function
-- in abstract mode, to have constructor Id in scope.
