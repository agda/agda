{-# OPTIONS --cubical-compatible #-}

module WithoutK-PatternSynonyms2 where

-- Equality defined with two indices.
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ x → x ≡ x

pattern r x = refl x

-- The --cubical-compatible option works with pattern synonyms.
K : (A : Set) (x : A) (P : x ≡ x → Set) → P (refl x) → (p : x ≡ x ) →  P p
K A .x P pr (r x) = pr
