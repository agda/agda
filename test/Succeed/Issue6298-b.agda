{-# OPTIONS --erased-cubical #-}

open import Agda.Builtin.Equality

data Unit : Set where
  unit : Unit

data D : Unit → Set where
  c : D unit

data P (_ _ : Unit) : Set where

F : (@0 x y : Unit) → @0 P x y → D x → Set₁
F _ _ _ c = Set
