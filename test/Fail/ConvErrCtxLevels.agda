module ConvErrCtxLevels where

open Agda.Primitive

record Set* (ℓ : Level) : Set (lsuc ℓ) where
  field
    S : Set ℓ
    x : S
open Set*

record Structure {ℓ}(A : Set* ℓ) : Set ℓ where
  field
    a b : A .S

module _ ℓ ℓ' (A : Set* (lsuc lzero ⊔ ℓ)) (B : Set* (lsuc lzero ⊔ ℓ')) where
  -- if equalLevel is not guarded by nowConversionChecking, this says
  --   Structure {ℓ} A != Structure {ℓ'} B
  -- which is not well typed because the zipper does not reflect that we
  -- skipped past the common 'lsuc lzero'
  attempt : Structure A → Structure B
  attempt b = b
