-- Andreas, 2022-06-24, allow several rewrite relations.

{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  R : (A : Set) → A → A → Set
  A : Set
  a b c : A
  foo : R A a b  -- using new rewrite relation
  bar : b ≡ c    -- using old rewrite relation

{-# BUILTIN REWRITE R #-}
{-# REWRITE foo bar #-}

test : a ≡ c
test = refl
