
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.List

it : {A : Set} → ⦃ A ⦄ → A
it ⦃ x ⦄ = x

opaque
  X : Set
  X = Nat

Number = Nat
record Count (A : Set) : Set where
  field count : A → Number

open Count ⦃...⦄ public

instance
  postulate Count-X : Count X

works : X → Nat
works s = count ⦃ it ⦄ s

opaque
  unfolding X
  works₂ : X → Nat
  works₂ s = count s

fails : X → Nat
fails s = count s
