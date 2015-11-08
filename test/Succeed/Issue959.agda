{-# OPTIONS --copatterns #-}

open import Common.Equality
open import Common.Product

id : {A : Set} → A → A
id x = x

record Functor (F : Set → Set) : Set₁ where
  field
    map : ∀ {A B} → (A → B) → F A → F B
    map-id : ∀ {A}{x : F A} → map id x ≡ x
open Functor

test : {C : Set} → Functor (_×_ C)
map    test f (c , a) = c , f a
map-id test           = refl -- : map test id x ≡ x
  -- needs to match against record constructor
  -- x/(c,a) = proj₁ x / c, proj₂ x / a
