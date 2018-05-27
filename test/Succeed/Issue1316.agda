-- Andreas, 2015-09-12, issue reported by F Mazzoli
-- {-# OPTIONS -v tc.meta.assign.proj:85 #-}

open import Common.Product
open import Common.Equality

module _ (A : Set) where

mutual
  X : A × A → A
  X = _

  test : (x y : A × A) → X (proj₁ x , proj₁ y) ≡ proj₁ x
  test x y = refl

-- In order to solve X, record variables x and y
-- have to be expanded.

-- Previously, this happend only if projections were
-- direct argument to the meta-variable.
-- Now, we also accept them inside record constructors.

verify : ∀{p} → X p ≡ proj₁ p
verify = refl
