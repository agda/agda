{-# OPTIONS --erasure --no-eta-singleton #-}

module Issue5703Works where

postulate
  _≡_  : {A : Set} → A → A → Set
  refl : (A : Set) (x : A) → x ≡ x

works :
  (@0 A : Set) (P : @0 A → Set) →
  (f : (@0 x : A) → P x) → f ≡ f
works A P f = refl ((@0 x : A) → P x) _
