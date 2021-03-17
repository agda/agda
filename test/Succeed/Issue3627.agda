open import Agda.Builtin.Bool

data ⊥ : Set where

record ⊤ : Set where

IsTrue : Bool → Set
IsTrue false = ⊥
IsTrue true = ⊤

record Squash {ℓ} (A : Set ℓ) : Set ℓ where
  field
    .unsquash : A
open Squash

f : .Bool → Squash Set₁
f b .unsquash = Set
  module M where
    IsTrue' : Set
    IsTrue' = IsTrue b

g : Squash Set₁
g .unsquash = Set
  module N where
    open M

    h : IsTrue' true → Set₁
    h p = Set
