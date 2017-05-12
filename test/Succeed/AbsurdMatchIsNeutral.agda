--{-# OPTIONS -v tc.pos:100 #-}

open import Agda.Builtin.Equality

data ⊥ : Set where

postulate
  A : Set
  R : A → Set

magic : ⊥ → A
magic ()

test : (a : ⊥) → magic a ≡ magic _
test a = refl
