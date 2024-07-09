{-# OPTIONS --no-keep-pattern-variables #-}

-- {-# OPTIONS -v tc.cover:40 #-}

-- Andreas, 2014-10-09
-- Reported by ohmanjoakim

infixr 8 _⇒_

data Ty : Set where
  _⇒_ : Ty → Ty → Ty

⟦_⟧ : Ty → Set
⟦ A ⇒ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧

data Term : Ty → Set where
  K : (A B : Ty) → Term (A ⇒ B ⇒ A)

test : (A : Ty) (a : Term A) → ⟦ A ⟧
test A a = {!a!}

-- When doing a case split on a in foo, the following is written:
-- test .(x ⇒ x₁ ⇒ x) (K A B) x x₁ = ?

-- Correct is
-- test .(A ⇒ B ⇒ A) (K A B) x x₁ = ?
