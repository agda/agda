{-# OPTIONS --no-keep-pattern-variables #-}
  -- Andreas, 2024-07-09.  According to
  -- https://github.com/agda/agda/issues/4704#issuecomment-778805747
  -- this test is pointless with --keep-pattern-variables.

open import Agda.Builtin.List
open import Agda.Builtin.Nat

infixl 6 _∷ʳ_

_∷ʳ_ : {A : Set} → List A → A → List A
[]        ∷ʳ x = x ∷ []
(hd ∷ tl) ∷ʳ x = hd ∷ tl ∷ʳ x

infixl 5 _∷ʳ′_

data InitLast {A : Set} : List A → Set where
  []    : InitLast []
  _∷ʳ′_ : (xs : List A) (x : A) → InitLast (xs ∷ʳ x)

initLast : {A : Set} (xs : List A) → InitLast xs
initLast []               = []
initLast (x ∷ xs)         with initLast xs
... | []       = [] ∷ʳ′ x
... | ys ∷ʳ′ y = (x ∷ ys) ∷ʳ′ y

f : (xs : List Nat) → Set
f xs with initLast xs
... | p = {!p!}
