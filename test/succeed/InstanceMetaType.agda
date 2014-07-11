module InstanceMetaType where

⟨⟩ : {A : Set} {{a : A}} → A
⟨⟩ {{a}} = a

postulate
  A : Set
  instance a : A
  f : (a : A) → Set

test₁ : Set
test₁ = f ⟨⟩


postulate
  B : Set
  b : B
  g : (b : B) → Set

instance
  b' : _
  b' = b

test₂ : Set
test₂ = g ⟨⟩

