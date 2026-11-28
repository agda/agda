{-# OPTIONS --erasure #-}
{-# OPTIONS --no-eta-singleton #-} -- type-checks without this

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Equality

variable
  ℓ : Level
  a : Set

if_then_else_ : {@0 a : Set ℓ} → (flg : Bool) → (@0 {{ flg ≡ true }} → a) → (@0 {{ flg ≡ false }} → a) → a
if false then x else y = y
if true  then x else y = x

filter : (a → Bool) → List a → List a
filter p []       = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs
