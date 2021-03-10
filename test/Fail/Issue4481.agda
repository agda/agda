-- Andreas, 2020-03-26, issue #4481, reported by gallais

-- #952 unintentionally added named lambdas, but without updating the type-checker.

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.term.expr.top:15 #-}
-- {-# OPTIONS -v tc.term.lambda:30 #-}

open import Agda.Primitive

-- In Agda 2.6.0 and 2.6.1, this is a fake inconsistency proof:

data ⊥ : Set where
record ⊤ : Set where

proj2 : ∀ a {A B : Set a} → Set a
proj2 = λ _ {B = B} → B

agdaIsInconsistent : proj2 lzero {⊤} {⊥}
agdaIsInconsistent = _  -- should be yellow in > 2.6.1

-- The following should complain about unexpected implicit argument:

_ : Set → {A B : Set} → Set
_ = λ _ {C = B} {A} → A  -- should fail
