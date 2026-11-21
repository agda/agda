{-# OPTIONS --double-check #-}

module Issue434 where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

record R (A : Set) : Set where
  field a : A

  choose : Bool → A
  choose b = {!!}

  field law : choose true ≡ a
