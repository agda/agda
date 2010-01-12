{-# OPTIONS --allow-unsolved-metas #-}

module LateExpansionOfRecordMeta where

postulate
  I : Set
  i : I
  A : I → Set
  a : A i

data D : Set₁ where
  d : (P : A i → Set) → P a → D

record R (P : A i → Set) : Set where
  field
    p : P a

record ID : Set₁ where
  field
    P   : (i : I) → A i → Set
    isR : R (P i)

at : ID → D
at id = d (ID.P id i) (R.p (ID.isR id))

postulate
  T  : D → Set
  F  : (id : ID) → T (at id) → Set
  id : ID

foo : T (at id) → Set
foo t = F _ t
