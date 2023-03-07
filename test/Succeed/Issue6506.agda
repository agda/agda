{-# OPTIONS --cubical --no-double-check #-}
module Issue6506 where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp ; primTransp to transp)

postulate
  A : Type
  B : Type
  p : A ≡ A
  i : I

ex : Type
ex = transp {λ i → lsuc lzero} (λ i → A ≡ A) i0 p i

-- Incorrect level in transp of PathP also leads to malformed
-- with-abstraction types(!)
test : Type → ex ≡ ex
test t with B
... | A = λ i → ex
