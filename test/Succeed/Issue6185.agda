{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Agda.Builtin.Cubical.Path

postulate A : Set

record R : Set where
  p : A → A ≡ A
  p a i = {!!}

  field a : A
