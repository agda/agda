{-# OPTIONS --no-positivity-check #-}
module IIDr where

open import LF
open import IID

OPr : (I : Set) -> Set1
OPr I = I -> OP I One

rArgs : {I : Set}(γ : OPr I)(U : I -> Set)(i : I) -> Set
rArgs γ U i = Args (γ i) U

-- The type of IIDrs
data Ur {I : Set}(γ : OPr I)(i : I) : Set where
  intror : rArgs γ (Ur γ) i -> Ur γ i

-- The elimination rule
elim-Ur : {I : Set}(γ : OPr I)(C : (i : I) -> Ur γ i -> Set) ->
	  ((i : I)(a : rArgs γ (Ur γ) i) -> IndHyp (γ i) (Ur γ) C a -> C i (intror a)) ->
	  (i : I)(u : Ur γ i) -> C i u
elim-Ur γ C m i (intror a) = m i a (induction (γ i) (Ur γ) C (elim-Ur γ C m) a)

-- Large elimination
elim-Ur₁ : {I : Set}(γ : OPr I)(C : (i : I) -> Ur γ i -> Set1) ->
	   ((i : I)(a : rArgs γ (Ur γ) i) -> IndHyp₁ (γ i) (Ur γ) C a -> C i (intror a)) ->
	   (i : I)(u : Ur γ i) -> C i u
elim-Ur₁ γ C m i (intror a) = m i a (induction₁ (γ i) (Ur γ) C (elim-Ur₁ γ C m) a)

