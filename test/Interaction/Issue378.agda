-- Andreas, 2012-11-06 this has been fixed with issue 655
module Issue378 where

infix  7 _≡_
infixl 9 _+_

postulate
  ℕ    : Set
  _≡_  : ℕ → ℕ → Set
  zero : ℕ
  _+_  : ℕ → ℕ → ℕ

postulate
  S₁ : ∀ {m n o} → m ≡ n → m ≡ o → n ≡ o
  S₅ : ∀ n → zero + n ≡ n

-- Calling Auto on the hole generates the invalid expression
-- S₁ (S₅ .n) (S₅ .n).
refl : ∀ {n} → n ≡ n
refl = {!-m!}
-- C-c C-a should work now
