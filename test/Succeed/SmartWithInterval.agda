{-# OPTIONS --cubical --smart-with #-}

import Agda.Builtin.Equality.Rewrite

open import Agda.Builtin.Unit
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

-- Example inspired by
-- https://agda.zulipchat.com/#narrow/channel/260790-cubical/topic/.E2.9C.94.20Splitting.20an.20interval.20in.20Agda.20Cubical/with/527580783

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

variable
  A B : Set
  x y : A

data ⊥ : Set where

absurd : ⊥ → A
absurd ()

+disj : inl x ≡ inr y → ⊥
+disj p = primTransp (λ i → P (p i)) i0 tt
  where
    P : A + B → Set
    P (inl _) = ⊤
    P (inr _) = ⊥

+inj₁ : _≡_ {A = A + B} (inl x) (inl y) → x ≡ y
+inj₁ {x = x} {y = y} p i with p i
... | inl z = z
... | inr z = absurd (+disj λ j → p (primIMin i j))
