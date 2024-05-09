module Issue7250.A where

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record Whatever {a} (A : Set a) : Set a where
  no-eta-equality
  field go : A → A

open Whatever ⦃ ... ⦄ public

instance
  Whatever-generic : {a : Level} {A : Set a} → Whatever A
  Whatever-generic .go = λ x → x
  {-# INCOHERENT Whatever-generic #-}

private
  test₁ : Bool
  test₁ = go true

  _ : test₁ ≡ true
  _ = refl

  test₂ : Nat
  test₂ = go 42

  _ : test₂ ≡ 42
  _ = refl
