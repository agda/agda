{-# OPTIONS --cubical --safe #-}
module Issue7033a where

open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)

data ⊥ : Set where
data ⊤ : Set where tt : ⊤
data D : Set where
  base  : D
  loop  : PathP (λ _ → D) base base
  other : D

onS¹ : D → Set
onS¹ base     = ⊤
onS¹ (loop i) = ⊤
onS¹ _        = ⊥

JEEPERS! : ⊥
JEEPERS! = transp (λ i → onS¹ (hcomp {φ = ~ i} (λ { j (i = i0) → base }) base)) i0 tt
