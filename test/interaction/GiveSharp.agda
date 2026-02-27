{-# OPTIONS --cohesion #-}
module GiveSharp where

open import Agda.Builtin.Equality

record Sharp (@♯ A : Set) : Set where
  constructor con
  field
    @♯ counit : A

unit : {A : Set} → A → Sharp A
unit a = {! con ? !}
