-- Andreas, 2012-03-15, example by Nisse
-- {-# OPTIONS --show-implicit -v tc.meta:20 #-}
module Issue585-17 where

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data ″ℕ″ : Set where
  suc : ″ℕ″ → ″ℕ″

replicate : {A : Set} → ″ℕ″ → A → List A
replicate (suc n) x = x ∷ replicate n x

data P (A B : Set) : List B → Set where
  p : (x : B) → P A B (x ∷ [])

data Q {A B xs} : List B → P A B xs → Set where
  q : ∀ {x xs p} → Q xs p → Q (x ∷ xs) p

foo : {A B : Set} (x : B) (n : ″ℕ″) → Q (replicate n x) (p {A = A} x)
foo x n = bar x n
  where
  bar : {B : Set} (x : B) (n : ″ℕ″) → Q (replicate n x) (p x)
  bar x (suc n) = q (bar x n)

