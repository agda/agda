module Issue8384 where

postulate
  Ar ACx ASig : Set
  ε : ACx
  Ty : (κ : ASig) (γ : ACx) → Ar → Set

variable
  a : Ar

data CstAr : Set where
  cst : (a : Ar) → CstAr

data CstTy (κ : ASig) : CstAr → Set where
  cst : (A : Ty κ ε) → CstTy κ (cst a)
