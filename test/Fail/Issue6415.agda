{-# OPTIONS --cubical --lossy-unification #-}
module Issue6415 where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Glue
open import Agda.Builtin.Cubical.Path

data S¹ : Type where
  base : S¹
  loop : base ≡ base

G : Type
G = primGlue S¹ {i0} isOneEmpty isOneEmpty

g : G
g = prim^glue (isOneEmpty {A = λ .p → isOneEmpty p}) base

hmm : primTransp (λ _ → G) i0 g ≡ g
hmm = Helpers.refl
