-- Andreas, 2016-11-03, issue #2292
-- Internal error when debugging the coverage checker.

{-# OPTIONS -v tc.cover.top:10 #-} -- KEEP!

data ⊥ : Set where

⊥-elim : ∀{A : Set} → ⊥ → A
⊥-elim ()
