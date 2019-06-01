{-# OPTIONS --rewriting --confluence-check #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data Unit : Set where
  unit : Unit

Foo : Unit → Set
Foo unit = Unit

Bar : Unit → Unit → Set
Bar unit = Foo

bar : ∀ x y → Bar x y ≡ Unit
bar unit unit = refl

{-# REWRITE bar #-}

test : ∀ x y → Bar x y
test _ _ = unit

works : ∀ x → Foo x
works x = test unit x
