{-# OPTIONS --cubical #-}

open import Agda.Primitive.Cubical
  renaming ( primIMin       to _∧_  -- I → I → I
           ; primIMax       to _∨_  -- I → I → I
           ; primINeg       to ~_   -- I → I
           )

infix 10 _≡_
postulate
  _≡_ : I → I → Set
  refl : ∀ {i} → i ≡ i


module Vars (i j k : I) where

  _ : i ∧ i1 ≡ i
  _ = refl

  _ : i ∧ i0 ≡ i0
  _ = refl

  _ : i1 ∧ i ≡ i
  _ = refl

  _ : i0 ∧ i ≡ i0
  _ = refl

  _ : i ∧ j ≡ j ∧ i
  _ = refl

  _ : i ∧ (j ∧ k) ≡ (i ∧ j) ∧ k
  _ = refl

  _ : i ∧ i ≡ i
  _ = refl

  _ : i ∨ j ≡ j ∨ i
  _ = refl

  _ : i ∨ (j ∨ k) ≡ (i ∨ j) ∨ k
  _ = refl

  _ : i ∨ i ≡ i
  _ = refl

  _ : i ∨ i1 ≡ i1
  _ = refl

  _ : i ∨ i0 ≡ i
  _ = refl

  _ : i1 ∨ i ≡ i1
  _ = refl

  _ : i0 ∨ i ≡ i
  _ = refl

  _ : ~ i0 ≡ i1
  _ = refl

  _ : ~ i1 ≡ i0
  _ = refl

  _ : ~ (~ i) ≡ i
  _ = refl

  _ : ~ (i ∧ j) ≡ ~ i ∨ ~ j
  _ = refl

  _ : ~ (i ∨ j) ≡ ~ i ∧ ~ j
  _ = refl

  _ : i ∧ (j ∨ k) ≡ (i ∧ j) ∨ (i ∧ k)
  _ = refl

  _ : i ∨ (j ∧ k) ≡ (i ∨ j) ∧ (i ∨ k)
  _ = refl

module Postulates where
  postulate
    i j k : I

  _ : i ∧ i1 ≡ i
  _ = refl

  _ : i ∧ i0 ≡ i0
  _ = refl

  _ : i1 ∧ i ≡ i
  _ = refl

  _ : i0 ∧ i ≡ i0
  _ = refl

  _ : i ∧ j ≡ j ∧ i
  _ = refl

  _ : i ∧ (j ∧ k) ≡ (i ∧ j) ∧ k
  _ = refl

  _ : i ∧ i ≡ i
  _ = refl

  _ : i ∨ j ≡ j ∨ i
  _ = refl

  _ : i ∨ (j ∨ k) ≡ (i ∨ j) ∨ k
  _ = refl

  _ : i ∨ i ≡ i
  _ = refl

  _ : i ∨ i1 ≡ i1
  _ = refl

  _ : i ∨ i0 ≡ i
  _ = refl

  _ : i1 ∨ i ≡ i1
  _ = refl

  _ : i0 ∨ i ≡ i
  _ = refl

  _ : ~ i0 ≡ i1
  _ = refl

  _ : ~ i1 ≡ i0
  _ = refl

  _ : ~ (~ i) ≡ i
  _ = refl

  _ : ~ (i ∧ j) ≡ ~ i ∨ ~ j
  _ = refl

  _ : ~ (i ∨ j) ≡ ~ i ∧ ~ j
  _ = refl

  _ : i ∧ (j ∨ k) ≡ (i ∧ j) ∨ (i ∧ k)
  _ = refl

  _ : i ∨ (j ∧ k) ≡ (i ∨ j) ∧ (i ∨ k)
  _ = refl
