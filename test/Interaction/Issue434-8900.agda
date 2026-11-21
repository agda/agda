-- Shared field-type holes (#8900) must also work with staged helpers (#434).
{-# OPTIONS --double-check #-}

module Issue434-8900 where

open import Agda.Builtin.Bool using (Bool; true; false)

record R (A : Set) (P : A → Set) : Set₁ where
  field seed : A

  pick : Bool → A
  pick true  = seed
  pick false = seed

  field X Y Z : (f : A → A) (a : A) → P {!!}

-- An enclosing record value is a genuine shared context entry, not something
-- to reconstruct from fields when reusing the inner record's interaction meta.
record Outer (A : Set) (P : A → Set) : Set₁ where
  field seed : A

  record Inner : Set₁ where
    field X Y Z : (f : A → A) (a : A) → P {!!}
