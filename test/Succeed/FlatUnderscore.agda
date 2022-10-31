{-# OPTIONS --cohesion #-}

module FlatUnderscore where


postulate
  A : Set
  f : (@♭ X : A → Set) → ∀ a → X a
  @♭ B : A → Set

-- The undescore should be solved to B.
g : ∀ a → B a
g = f _
