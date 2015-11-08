{-# OPTIONS --copatterns --sized-types #-}

open import Common.Size

module Issue1038 (A : Set) where

record S (i : Size) : Set where
  field
    force : ∀ (j : Size< i) → A

head : ∀ i → S i → (j : Size< i) → A
head i s j = S.force s _

-- Problem was:
-- Cannot solve size constraints
-- (↑ _9 A i s j) =< (_i_8 A i s j) : Size
-- (_i_8 A i s j) =< i : Size
-- when checking the definition of head

-- Works now.
