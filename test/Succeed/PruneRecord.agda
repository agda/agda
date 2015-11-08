-- 2014-06-02 Andrea & Andreas

module _ where

open import Common.Equality
open import Common.Product

postulate
  A : Set
  F : Set → Set

test : let M : Set
           M = _
           N : Set × Set → Set
           N = _
       in  ∀ {X : Set}
           → M ≡ F (N (X , X))
           × N (A , A) ≡ A
test = refl , refl

-- Here, we can prune the argument of N,
-- since M does not depend on X,
-- and the argument is a pair with a bad rigid
-- in *each* component.
