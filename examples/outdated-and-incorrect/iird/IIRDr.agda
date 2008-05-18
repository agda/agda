{-# OPTIONS --no-positivity-check #-}
module IIRDr where

import LF
import IIRD

open LF
open IIRD

-- Agda2 has restricted IIRDs so we can define Ur/Tr directly

mutual
  data Ur {I : Set}{D : I -> Set1}(γ : OPr I D)(i : I) : Set where
    intror : Hu γ (Ur γ) (Tr γ) i -> Ur {I}{D} γ i

  Tr : {I : Set}{D : I -> Set1}(γ : OPr I D)(i : I) -> Ur γ i -> D i
  Tr γ i (intror a) = Ht γ (Ur γ) (Tr γ) i a

-- Elimination rule
Rr : {I : Set}{D : I -> Set1}(γ : OPr I D)(F : (i : I) -> Ur γ i -> Set1)
     (h : (i : I)(a : Hu γ (Ur γ) (Tr γ) i) -> KIH (γ i) (Ur γ) (Tr γ) F a -> F i (intror a))
     (i : I)(u : Ur γ i) -> F i u
Rr γ F h i (intror a) = h i a (Kmap (γ i) (Ur γ) (Tr γ) F (Rr γ F h) a)

-- Helpers

ι★r : {I : Set}{D : I -> Set1} -> OP I D One'
ι★r = ι ★'

