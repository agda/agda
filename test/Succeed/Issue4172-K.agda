{-# OPTIONS --with-K --erasure #-}

-- Andreas 2019-11-06, issue #4172, examples by nad.

-- Single constructor matches for non-indexed types should be ok
-- even when argument is erased, as long as pattern variables
-- are only used in erased context on the rhs.

-- https://github.com/agda/agda/issues/4172#issue-517690102

record Erased (A : Set) : Set where
  constructor [_]
  field
    @0 erased : A

open Erased

data W (A : Set) (B : A → Set) : Set where
  sup : (x : A) → (B x → W A B) → W A B

lemma :
  {A : Set} {B : A → Set} →
  Erased (W A B) → W (Erased A) (λ x → Erased (B (erased x)))
lemma [ sup x f ] = sup [ x ] λ ([ y ]) → lemma [ f y ]

-- https://github.com/agda/agda/issues/4172#issuecomment-549768270

data ⊥ : Set where

data E : Set where
  c : E → E

magic : @0 E → ⊥
magic (c e) = magic e

-- Two more examples.

open import Agda.Builtin.Equality

subst-erased : {A : Set} {x y : A} (P : A → Set) → @0 x ≡ y → P x → P y
subst-erased P refl p = p

open import Agda.Builtin.Bool

data D : Bool → Set where
  true  : D true
  false : D false

F : @0 D false → Set₁
F false = Set
