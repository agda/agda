open import Agda.Builtin.Equality using (_≡_; refl)

record ⊤ : Set where
  no-eta-equality
  constructor tt

data Box (A : Set) : Set where
  [_] : A → Box A

Unit : Set
Unit = Box ⊤

F : Unit → Set → Set
F [ _ ] x = x

G : {P : Unit → Set} → ((x : ⊤) → P [ x ]) → ((x : Unit) → P x)
G f [ x ] = f x

record R : Set₁ where
  no-eta-equality
  field
    f : (x : Unit) → Box (F x ⊤)

  data ⊥ : Set where

r : R
r = record { f = G [_] }

open R r

H : ⊥ → Set₁
H _ rewrite refl {x = tt} = Set
