-- Andreas, 2020-03-26, issue #4481, reported by gallais

-- #952 unintentionally added named lambdas; tests here.

-- {-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.term.expr.top:15 #-}
-- {-# OPTIONS -v tc.term.lambda:30 #-}

open import Agda.Primitive

-- Named lambdas:

postulate f : ({A : Set} → Set) → Set
_ = f λ {A = A} → A

postulate
  A : Set
  g : ({{a : A}} → A) → A
_ = g λ {{a = a}} → a

data ⊥ : Set where
record ⊤ : Set where

proj2 : ∀ a {A B : Set a} → Set a
proj2 = λ _ {B = B} → B

agdaIsConsistent : proj2 lzero {⊥} {⊤}
agdaIsConsistent = _
