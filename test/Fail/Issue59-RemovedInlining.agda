-- Jesper, 2019-05-21: this is the old test case for the removed
-- with-inlining feature
module Issue59-RemovedInlining where

open import Common.Prelude
open import Common.Equality

module Order (A : Set) (_≤_ : A → A → Bool) where

  -- This now termination checks.
  merge : List A → List A → List A
  merge [] ys = ys
  merge xs [] = xs
  merge (x ∷ xs) (y ∷ ys) with x ≤ y
  merge (x ∷ xs) (y ∷ ys)      | false = y ∷ merge (x ∷ xs) ys
  merge (x ∷ []) (y ∷ ys)      | true  = x ∷ y ∷ ys
  merge (x ∷ x₁ ∷ xs) (y ∷ ys) | true  = x ∷ merge (x₁ ∷ xs) (y ∷ ys)

data Ordering : Nat → Nat → Set where
  eq : ∀ n → Ordering n n
  lt : ∀ n d → Ordering n (n + suc d)
  gt : ∀ n d → Ordering (n + suc d) n

-- Just make sure we didn't mess anything up when there are dot patterns.
-- Andreas, 2013-11-11: But there are no recursive calls in the clauses
-- with dot patterns!

compare : ∀ n m → Ordering n m
compare zero zero = eq zero
compare zero (suc m) = lt zero m
compare (suc n) zero = gt zero n
compare (suc n) (suc m) with compare n m
compare (suc n) (suc .(n + suc d)) | lt .n d = lt (suc n) d
compare (suc .(m + suc d)) (suc m) | gt .m d = gt (suc m) d
compare (suc n) (suc .n)           | eq .n = eq (suc n)

-- Rewrite

plus-zero : ∀ n → n + 0 ≡ n
plus-zero zero = refl
plus-zero (suc n) rewrite plus-zero n = refl

plus-suc : ∀ n m → n + suc m ≡ suc n + m
plus-suc zero m = refl
plus-suc (suc n) m rewrite plus-suc n m = refl

commute : ∀ m n → m + n ≡ n + m
commute m zero = plus-zero m
commute m (suc n) rewrite plus-suc m n | commute m n = refl
