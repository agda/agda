{-# OPTIONS --allow-unsolved-metas #-}

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
... | [] = {!!}
... | xs ∷ʳ′ x = {!!}

-- ^ Shadowing a variable that is bound implicitly in the `...` is allowed
