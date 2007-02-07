
open import Category

module Iso (ℂ : Cat) where

private open module C = Cat (η-Cat ℂ)

data _≅_ (A B : Obj) : Set where
  iso : (i : A ─→ B)(j : B ─→ A) ->
	i ∘ j == id -> j ∘ i == id ->
	A ≅ B

