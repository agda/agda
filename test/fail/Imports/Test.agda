{-# OPTIONS --universe-polymorphism #-}
module Imports.Test where

open import Imports.Level

record Foo (ℓ : Level) : Set ℓ where

