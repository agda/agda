{-# OPTIONS --cohesion #-}
module GiveSharp where

open import Agda.Builtin.Equality

data Sharp (@♯ A : Set) : Set where
  con : (@♯ x : A) → Sharp A

{-# MODALOP Sharp #-}

unit : {A : Set} → A → Sharp A
unit a = {! con ? !}
