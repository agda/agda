
-- Overlapping instances are only allowed if all valid candidates are
-- overappable.

module _ where

postulate
  A : Set

record B : Set where
  field overlap {{a}} : A

record C : Set where
  field overlap {{a}} : A

record D : Set where
  field {{a}} : A

it : ∀ {a} {A : Set a} {{_ : A}} → A
it {{x}} = x

work : {{b : B}} {{c : C}} → A
work = it

-- One variable candidate
fail₁ : {{a : A}} {{b : B}} → A
fail₁ = it

-- One non-overlappable field candidate
fail₂ : {{c : C}} {{d : D}} → A
fail₂ = it

instance postulate a : A

-- One top-level candidate
fail₃ : {{b : B}} → A
fail₃ = it
