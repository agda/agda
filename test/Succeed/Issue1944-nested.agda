-- Andreas, AIM XXIII, Issue 1944

-- {-# OPTIONS -v tc.proj.amb:30 #-}

-- Non-overloaded

record Wrap (A : Set) : Set where
  field wrapped : A
open Wrap

-- Overloaded

record Sg (A : Set) : Set where
  field head : A
open Sg

record Sg' (A : Set) : Set where
  field head : A
open Sg'

-- ov/ov

works : ∀ {A : Set} (w : Sg (Sg' A)) → Sg A
head (works w) = head (head w)

-- ov/nov

test : ∀ {A : Set} (w : Wrap (Sg' A)) → Sg A
head (test w) = head (wrapped w)

-- WAS: failed because of a missing `reduce`
