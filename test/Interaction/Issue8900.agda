-- Giving shared interaction metas must preserve parameters, earlier fields,
-- and variables bound inside the shared field type.

{-# OPTIONS --double-check #-}

module Issue8900 where

-- Fix the sort of the type hole so loading leaves only interaction metas.
asSet : Set → Set
asSet T = T

record Types (A : Set) (P : A → Set) : Set₁ where
  field
    seed : A
    X Y Z : (f : A → A) (a : A) → asSet {!!}

record Values (A : Set) (P : A → Set) (choose : A → A → A) : Set₁ where
  field
    seed : A
    X Y Z : (f : A → A) (a : A) → P {!!}

-- The preceding fields have the same names as the local binders.
record Shadowing (A : Set) (P : A → Set) (choose : A → A → A) : Set₁ where
  field
    seed : A
    f a Z : (f : A → A) (a : A) → P {!!}
