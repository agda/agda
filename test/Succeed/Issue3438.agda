{-# OPTIONS --prop --type-in-type #-}

open import Agda.Primitive

data Squash (A : Setω) : Prop where
  squash : A → Squash A
