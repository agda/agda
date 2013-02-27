-- {-# OPTIONS -v tc.inj:100 -v tc.reduce:100 #-}
module Issue801 where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

cong : ∀ {A : Set} {B : Set}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

lem : (n : ℕ) → n ≡ n
lem zero    = refl
lem (suc n) = cong (λ x → x) (lem (suc n))
-- Andreas: this made the injectivity checker loop.
-- Now it should just report a termination error.
