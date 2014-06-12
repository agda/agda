-- Andreas, 2014-06-12  This feature has been addressed by issue 907

{-# OPTIONS --copatterns #-}

module CopatternsToRHS where

import Common.Level
open import Common.Equality
open import Common.Prelude using (Bool; true; false)

record R (A : Set) : Set where
  constructor mkR
  field
    fst : A → A
    snd : Bool
open R

someR : {A : Set} → R A
fst someR x = x
snd someR = true

-- This already behaves like:

someR' : {A : Set} → R A
fst someR' = λ x → x
snd someR' = true

-- We translate it to:

someR″ : {A : Set} → R A
someR″ = mkR (λ x → x) true

data C {A : Set} : R A → Set where
   c : ∀ f b → C (mkR f b)

works : {A : Set} → C {A} someR″ → Set₁
works (c .(λ x → x) .true) = Set

test : {A : Set} → C {A} someR → Set₁
test (c .(λ x → x) .true) = Set
