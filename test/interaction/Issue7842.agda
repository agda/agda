-- Andreas, 2025-05-02, issue #7842, reported and testcase by Nisse
-- Catch pattern violation during give.

{-# OPTIONS --erasure #-}

data _≡_ {@0 a} {@0 A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

postulate
  subst :
    ∀ {@0 a} {p} {@0 A : Set a} {x y : A}
    (P : A → Set p) → x ≡ y → P x → P y

cong :
  ∀ {@0 a} {b} {A : Set a} {B : Set b} {x y : A}
  (f : A → B) → x ≡ y → f x ≡ f y
cong {x = x} f eq = {!subst (λ y → x ≡ y → f x ≡ f y) ? ? eq!}

-- Giving should not cause a panic.
