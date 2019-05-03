-- Andreas, 2019-05-03, issue #3742, reported by nad
--
-- Regression introduced in 2.5.2:
--
-- getConstInfo applied to abstract constructor D.c
-- in metaOccurs check throws funny "not in scope" error for D.c

record Σ (A : Set) (B : A → Set₁) : Set₁ where

mutual

  abstract

    data D (A : Set) : Set where
      c : D A

  F : Set → Set₁
  F A = Σ _ λ (_ : D A) → Set

-- Should succeed.
