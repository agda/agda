{-# OPTIONS --no-keep-pattern-variables #-}
{-# OPTIONS --sized-types #-}

-- Jesper, 2017-01-24: if we allow a variable to be instantiated with a value
-- of a supertype, the resulting dot pattern won't be type-correct.

open import Common.Size

data D (i : Size) : (j : Size< ↑ i) → Set where

  c : ∀ (j : Size< ↑ i) (k : Size< ↑ j)
       → D i j
       → D j k
       → D i k

split : ∀ i (j : Size< ↑ i) → D i j → Set
split i j x = {!x!}  -- split on x

-- Expected: splitting on x succeeds with
--   split i .k (c j k x x₁) = {!!}
