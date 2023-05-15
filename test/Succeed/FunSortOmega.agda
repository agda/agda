-- Andreas, 2023-05-17, end of AIM XXXVI
-- Determine codomain sort from ω-funSort and smaller domain sort.
-- For SSetω, determine even domain from smaller codomain.

{-# OPTIONS --two-level #-}
{-# OPTIONS --prop #-}

module _ where

open Agda.Primitive
open import Agda.Primitive.Cubical

module PropOmega where

  _ : Set → _ → Propω
  _ = λ A B → A → B

  _ : Prop → _ → Propω
  _ = λ A B → A → B

module SetOmega where

  _ : Set → _ → Setω
  _ = λ A B → A → B

  _ : Prop → _ → Setω
  _ = λ A B → A → B

module SSetOmega where

  _ : Set → _ → SSetω
  _ = λ A B → A → B

  _ : Prop → _ → SSetω
  _ = λ A B → A → B

  _ : _ → Set → SSetω
  _ = λ A B → A → B

  _ : _ → Prop → SSetω
  _ = λ A B → A → B

module PropOmega1 where

  _ : Setω → _ → Propω1
  _ = λ A B → A → B

  _ : Propω → _ → Propω1
  _ = λ A B → A → B

module SetOmega1 where

  _ : Setω → _ → Setω1
  _ = λ A B → A → B

  _ : Propω → _ → Setω1
  _ = λ A B → A → B

module SSetOmega1 where

  _ : Setω → _ → SSetω1
  _ = λ A B → A → B

  _ : Propω → _ → SSetω1
  _ = λ A B → A → B

  _ : _ → Setω → SSetω1
  _ = λ A B → A → B

  _ : _ → Propω → SSetω1
  _ = λ A B → A → B
