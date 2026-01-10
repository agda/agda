module ConvErrCtxPi2 where

open Agda.Primitive

postulate T1 T2 X Y : Set

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
  attempt : foo {a = Structure {T1 → X} A} → foo {a = Structure {T1 → Y} B}
  attempt b = b

