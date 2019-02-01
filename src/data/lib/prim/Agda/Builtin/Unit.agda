{-# OPTIONS --without-K --safe --no-universe-polymorphism --no-sized-types --no-guardedness #-}

module Agda.Builtin.Unit where

record ⊤ : Set where
  instance constructor tt

{-# BUILTIN UNIT ⊤ #-}
{-# COMPILE GHC ⊤ = data () (()) #-}
