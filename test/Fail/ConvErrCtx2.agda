module ConvErrCtx2 where

open Agda.Primitive

postulate T1 T2 : Set

record Set* (ℓ : Level) : Set (lsuc ℓ) where
  field
    S : Set ℓ
    x : S
open Set*

record Structure {X : Set} {ℓ}(A : Set* ℓ) : Set ℓ where
  field
    a b : A .S

postulate
  foo : ∀ {ℓ} {X : Set ℓ} {a : X} → Set
  bar : Set → Set

module _ ℓ (A B : Set* ℓ) where
  attempt : foo {a = Structure {bar T1} A} → foo {a = Structure {bar T2} B}
  attempt b = b
