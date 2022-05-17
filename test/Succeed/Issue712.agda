{-# OPTIONS --cubical-compatible #-}

module Issue712 where

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

record _×_ (A B : Set) : Set where
  field
    p1 : A
    p2 : B
open _×_

lemma : {A B : Set} {u v : A × B} (p : u ≡ v) → p1 u ≡ p1 v
lemma (refl _) = refl _
