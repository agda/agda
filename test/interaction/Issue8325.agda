-- Andreas, 2026-01-20, issue #8325, shrunk test supplied by Maykeye
-- Internal error in refine.

-- {-# OPTIONS -v impossible:100 #-}

module _ where

data ℕ : Set where
  zero : ℕ
  suc : (n : ℕ) → ℕ

data Fin : ℕ → Set where
  fzero : ∀{n} → Fin (suc n)
  fsuc  : ∀{n} (i : Fin n) → Fin (suc n)

data Vec (A : Set) : ℕ → Set where
  [] : Vec A zero
  _∷_ : ∀{n} (x : A) (xs : Vec A n) → Vec A (suc n)

postulate
  elim : ∀ (P : ∀(k : ℕ) → Fin k → Set)
    → (∀{k} → P (suc k) fzero)
    → (∀{k} {fn : Fin k} → P k fn → P (suc k) (fsuc fn))
    → {k : ℕ} → (fn : Fin k) → P k fn

foo : ∀ {A : Set} {n} → Vec A n → Fin n → Vec A n
foo {A = A} {n = n} vec = elim
    (λ k i → Vec A k)
    {! (λ {k} (y ∷ ys) → y ∷ ys)  !} -- <<<<<<<< C-c C-r this hole
    {!   !}
