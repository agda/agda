{-# OPTIONS --type-in-type #-}

module _ where

Set' : ∀ i → Set _
Set' i = Set i

postulate
  A : Set
  a : A
  T : Set → Set
  comp : (P : A → Set) (g : (a : A) → P a) → P a
  foo : ∀ i (Q : A → Set' i) → T (comp _ Q)
  -- (no issue if Set' is replaced by Set)

bar : T {!_!} -- Try to give _
bar = foo _ _

-- WAS:
-- A !=< Agda.Primitive.Level of type Set
-- when checking that the expression _ has type Set
-- SHOULD: succeed (with unsolved meta)
