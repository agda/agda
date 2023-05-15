-- Andreas, 2023-05-17, end of AIM XXXVI
-- Determine codomain sort from ω-funSort and smaller domain sort.
-- In absence of Prop, determine even domain from smaller codomain.

{-# OPTIONS --two-level #-}

module _ where

open Agda.Primitive
open import Agda.Primitive.Cubical

module SetOmega where

  _ : Set → _ → Setω
  _ = λ A B → A → B

  _ : _ → Set → Setω
  _ = λ A B → A → B

module SSetOmega where

  _ : Set → _ → SSetω
  _ = λ A B → A → B

  _ : _ → Set → SSetω
  _ = λ A B → A → B

module SetOmega1 where

  _ : Setω → _ → Setω1
  _ = λ A B → A → B

  _ : _ → Setω → Setω1
  _ = λ A B → A → B

module SSetOmega1 where

  _ : Setω → _ → SSetω1
  _ = λ A B → A → B

  _ : _ → Setω → SSetω1
  _ = λ A B → A → B
