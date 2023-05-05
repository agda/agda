{-# OPTIONS --cubical --erasure --safe #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive

private
  variable
    a   : Level
    A B : Set a

Is-proposition : Set a → Set a
Is-proposition A = (x y : A) → x ≡ y

data ∥_∥ (A : Set a) : Set a where
  ∣_∣        : A → ∥ A ∥
  @0 trivial : Is-proposition ∥ A ∥

rec : @0 Is-proposition B → (A → B) → ∥ A ∥ → B
rec p f ∣ x ∣           = f x
rec p f (trivial x y i) = p (rec p f x) (rec p f y) i
