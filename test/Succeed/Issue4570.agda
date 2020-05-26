{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Primitive

record Graph ℓv ℓe : Set (lsuc (ℓv ⊔ ℓe)) where
  field
    Obj : Set ℓv
    Hom : Obj → Obj → Set ℓe

open Graph public

postulate
  t : Nat → Nat → Bool

ωGr : Graph lzero lzero
Obj ωGr = Nat
Hom ωGr m n with t m n
... | true = {!!} -- if n ≡ (suc m)
... | false = {!!} -- otherwise

foo : ∀ m n → Hom ωGr m n → {!!}
foo m n f with t m n
... | z = {!!}
