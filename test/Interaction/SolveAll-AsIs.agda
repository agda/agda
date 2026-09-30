module SolveAll-AsIs where

open import Common.Equality
open import Common.List
open import Common.Nat

example = 0 ∷ 1 ∷ 2 ∷ []

test1 : length example ≡ {!!}
test1 = refl

reverse : {A : Set} → List A → List A
reverse = go [] where

  go : {A : Set} → List A → List A → List A
  go acc []       = acc
  go acc (x ∷ xs) = go (x ∷ acc) xs

test2 : reverse example ≡ {!!}
test2 = refl
