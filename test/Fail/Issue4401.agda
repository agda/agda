{-# OPTIONS --cumulativity #-}

open import Agda.Builtin.Equality

mutual

  _X : (Set → Set) → Set₁ → Set
  _X f x = _

  test : (f : Set₁ → Set) (x : Set₁) → _X f x ≡ f x
  test f x = refl

Set' : Set
Set' = _X (λ X → X) Set
