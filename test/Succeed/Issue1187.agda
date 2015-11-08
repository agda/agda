-- Andreas, 2014-06-11, issue reported by Ulf
-- {-# OPTIONS -v tc.check.internal:100 -v tc.conv.elim:40 #-}

postulate
  Nat  : Set
  zero : Nat

module Projection where

  record _×_ (A B : Set) : Set where
    field fst : A
          snd : B
  open _×_

  postulate
    T    : (Nat × Nat → Nat) → Set
    foo  : T fst → Nat

  works : T fst → Nat
  works t with foo t
  works t | z = zero


module ProjectionLike where

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  fst : {A B : Set} → A × B → A
  fst (x , y) = x

  postulate
    T    : (Nat × Nat → Nat) → Set
    foo  : T fst → Nat

  -- Error WAS::
  -- {A B : Set} → A × B → A != Nat × Nat → Nat because one is an
  -- implicit function type and the other is an explicit function type
  -- when checking that the type (t : T fst) → Nat → Nat of the
  -- generated with function is well-formed
  test : T fst → Nat
  test t with foo t
  test t | z = zero

-- Problem WAS:
-- It looks like CheckInternal doesn't handle projection-like functions
-- correctly. It works for actual projections (if you make _×_ a record)
-- and non-projection-like functions (if you make fst a postulate).

-- Should work without error.
