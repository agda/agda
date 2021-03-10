{-# OPTIONS --cumulativity #-}

open import Agda.Primitive

-- Defaulting of level metas does not apply to interaction metas, so
-- the type of test₁ should be `Set ?0`, not `Set`.
test₁ : Set {!!}
test₁ = {!!}

postulate
  F : ∀ a (A : Set a) → A → Set

-- In this example, t first argument of F should not default to lzero
-- because it occurs in the type of another meta.
test₂ : F _ _ _
test₂ = {!!}
