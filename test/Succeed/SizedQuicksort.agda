-- 2014-04-24

{-# OPTIONS --sized-types #-}

module _ where

open import Common.Size
open import Common.Prelude using (Bool; true; false; if_then_else_)
open import Common.Product

-- sized lists

data List (A : Set) {i} : Set where
  []  : List A
  _∷_ : {i' : Size< i} (x : A) (xs : List A {i'}) → List A

_++_ : ∀{A} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

partition : ∀{A i} (p : A → Bool) (l : List A {i}) → List A {i} × List A {i}
partition p []       = [] , []
partition p (x ∷ xs) = let l , r = partition p xs in
  if p x then ((x ∷ l) , r) else (l , (x ∷ r))

module Sort {A : Set} (_≤_ : A → A → Bool) where

  quicksort : ∀{i} → List A {i} → List A
  quicksort []       = []
  quicksort (x ∷ []) = x ∷ []
  quicksort (x ∷ xs) = let x≤ , ≤x = partition (_≤_ x) xs in
    quicksort ≤x ++ (x ∷ quicksort x≤)
