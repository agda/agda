-- Andreas, 2012-03-09, example by Ulf
-- {-# OPTIONS -v tc.conv.irr:50 -v tc.decl.ax:10 -v tc.decl.mutual:20 #-}
module Issue351-5 where

open import Common.Prelude
open import Common.Equality
open import Common.Irrelevance

postulate
  foo : (x : Squash Nat) → ((r : Squash Nat) → r ≡ squash (suc (unsquash x))) → Set
  bar : foo (squash _) (λ r → refl)
