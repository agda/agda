
data   ⊥ : Set where
record ⊤ : Set where

data Bool : Set where
  false : Bool
  true  : Bool

True : Bool → Set
True false = ⊥
True true  = ⊤

Foo : (b : Bool) → True b → Set
Foo true  _  = ⊤
-- The problem rises because I have removed this impossible case.
-- Foo false ()

test : (b : Bool) (t : True b) → Foo b t → ⊤
test true  p x = _
test false p x = _
