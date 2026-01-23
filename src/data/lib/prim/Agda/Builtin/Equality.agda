{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erasure #-}

module Agda.Builtin.Equality where

infix 4 _≡_
data _≡_ {@0 a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
