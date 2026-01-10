module ConvErrCtx1 where

open Agda.Primitive

record Set* (ℓ : Level) : Set (lsuc ℓ) where
  field
    S : Set ℓ
    x : S
open Set*

record Structure {ℓ}(A : Set* ℓ) : Set ℓ where
  field
    a b : A .S

module _ ℓ ℓ' (A : Set* ℓ) (B : Set* ℓ') where
  attempt : Structure B → Structure A
  attempt b = b
