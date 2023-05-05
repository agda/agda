{-# OPTIONS --cubical-compatible --safe --no-universe-polymorphism
            --no-sized-types --no-guardedness --level-universe #-}

module Agda.Builtin.Unit where

record ⊤ : Set where
  instance constructor tt

{-# BUILTIN UNIT ⊤ #-}
{-# COMPILE GHC ⊤ = data () (()) #-}
