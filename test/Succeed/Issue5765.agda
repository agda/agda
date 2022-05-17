{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Equality

postulate @0 A : Set

@0 f : (X : Set) → A ≡ X → Set
f X refl = {!!}
