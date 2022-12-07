{-# OPTIONS --erasure #-}

-- Andreas, 2018-10-17, re #2757
--
-- Don't project from erased matches.

open import Agda.Builtin.List
open import Common.Prelude

data IsCons {A : Set} : List A → Set where
  isCons : ∀{@0 x : A} {@0 xs : List A} → IsCons (x ∷ xs)

headOfErased : ∀{A} (@0 xs : List A) → IsCons xs → A
headOfErased (x ∷ xs) isCons = x

-- Should fail with error:
--
-- Variable x is declared erased, so it cannot be used here

main = printNat (headOfErased (1 ∷ 2 ∷ []) isCons)

-- Otherwise, main segfaults.
