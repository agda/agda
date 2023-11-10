{-# OPTIONS --opaque #-}

open import Agda.Builtin.Equality

mutual

  F : Set₁ → Set₁
  F A = A

  _ : F Set ≡ Set
  _ = refl

data D : Set where

G : Set → Set
G A = A
  where
  B : Set
  B = A

  _ : A ≡ B
  _ = refl

H : Set → Set
H A = let B = A in B

record R : Set₁ where

  -- Definitions before the last field declaration in a record type
  -- cannot be made opaque.

  A : Set₂
  A = Set₁

  a₁ : A
  a₁ = Set

  field
    B : Set

  a₂ : A
  a₂ = Set

postulate
  r : R

open R r

a₃ : A
a₃ = Set

transparent

  C : Set₁
  C = Set

_ : C ≡ Set
_ = refl
