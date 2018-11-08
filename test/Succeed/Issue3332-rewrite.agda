-- Jesper, Andreas, 2018-10-29, issue #3332
--
-- WAS: With-inlining failed in termination checker
-- due to a DontCare protecting the clause bodies
-- (introduced by Prop).

{-# OPTIONS --prop #-}

data _≡_ {A : Set} (a : A) : A → Prop where
  refl : a ≡ a
{-# BUILTIN EQUALITY _≡_ #-}

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
[] ++ l = l
(x ∷ xs) ++ l = x ∷ (xs ++ l)

test : {A : Set} (l : List A) → (l ++ []) ≡ l
test [] = refl
test (x ∷ xs) rewrite test xs = refl
