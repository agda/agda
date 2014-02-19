
data _≡_ {A : Set}(x : A) : A → Set where
  refl : x ≡ x

data * : Set where ! : *

postulate
  prop : ∀ x → x ≡ !

record StrictTotalOrder : Set where
  field compare : *

open StrictTotalOrder

module M (Key : StrictTotalOrder) where

    postulate
      intersection′-₁ : ∀ x → x ≡ compare Key

    -- Doesn't termination check, but shouldn't get __IMPOSSIBLE__
    -- when termination checking!
    to-∈-intersection′  : * → * → Set
    to-∈-intersection′ x h with intersection′-₁ x
    to-∈-intersection′ ._ h   | refl with prop h
    to-∈-intersection′ ._ ._  | refl    | refl = to-∈-intersection′ ! !
