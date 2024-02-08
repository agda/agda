{-# OPTIONS --cubical --safe #-}
module Issue7033b where

open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)

data ⊥ : Set where
data ⊤ : Set where tt : ⊤

data D : ⊤ → Set where
    c1 : D tt
    c2 : D tt

isC1 : {A : ⊤} → D A → Set
isC1 c1 = ⊤
isC1 _  = ⊥

JEEPERS! : ⊥
JEEPERS! = transp (λ i → isC1 (transp (λ j → D tt) (~ i) c1)) i0 tt
