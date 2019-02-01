{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality

data Colist (A : Set) : Set where
  [] : Colist A
  _∷_ : A → ∞ (Colist A) → Colist A

from : Nat → Colist Nat
from n = let sn = suc n in n ∷ ♯ (from sn)

take : {A : Set} → Nat → Colist A → List A
take zero    xs = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

check : take 3 (from 5) ≡ 5 ∷ 6 ∷ 7 ∷ []
check = refl
