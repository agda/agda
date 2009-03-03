-- Tests unreachable clause detection
module Unreachable where

data C : Set where
  c₁ : C
  c₂ : C -> C

data Bool : Set where
  t : Bool
  f : Bool

maj : Bool -> Bool -> Bool -> Bool
maj f f f = f
maj t f x = x
maj f x t = x
maj x t f = x
maj t t t = t

unreachable : C -> C
unreachable (c₂ x)      = c₁
unreachable (c₂ (c₂ y)) = c₂ c₁
unreachable c₁          = c₁
unreachable _ = c₁