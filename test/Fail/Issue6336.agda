-- This example is due to David Wärn.

{-# OPTIONS --cubical --safe #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Bool

data A (f : Set → Bool) : Set where
  g : Bool → A f
  p : g (f (A f)) ≡ g true
