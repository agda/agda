-- Andreas, 2019-11-06 issue #4168, version with shape-irrelevance.

-- Eta-contraction of records with all-irrelevant fields is unsound.
-- In this case, it lead to a compilation error.

{-# OPTIONS --irrelevant-projections #-}

-- {-# OPTIONS -v tc.cc:20 #-}

open import Agda.Builtin.Unit
open import Common.IO using (IO; return)

main : IO ⊤
main = return _

record Box (A : Set) : Set where
  constructor box
  field
    ..unbox : A

open Box

record R (M : Set → Set) : Set₁ where
  field
    bind : (A B : Set) → M A → (A → M B) → M B
open R

works : R Box
works .bind A B x g .unbox = unbox (g (unbox x))

test : R Box
test .bind A B x g = box (unbox (g (unbox x)))
-- WAS eta-contracted to: test .bind A B x g = g (unbox x)
-- crashing compilation.

-- Compilation should succeed.
