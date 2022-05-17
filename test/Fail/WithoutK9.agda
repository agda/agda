{-# OPTIONS --cubical-compatible --show-implicit #-}
-- {-# OPTIONS -v tc.data:100 #-}
module WithoutK9 where

module Eq {A : Set} (x : A) where

  data _≡_ : A → Set where
    refl : _≡_ x

open Eq

module Bad {A : Set} {x : A} where

  module E = Eq x

  weak-K : {y : A} (p q : E._≡_ y) (α β : p ≡ q) → α ≡ β
  weak-K refl .refl refl refl = refl

