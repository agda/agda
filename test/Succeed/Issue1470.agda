-- Andreas, 2015-03-26

-- Andrea discovered that unfold for Lists is typable with sized types
-- (and termination checks).
-- Dually, fold for Streams should work.  Therefore, the restriction
-- of coinductive records to recursive records should be lifted.

{-# OPTIONS --copatterns --sized-types #-}

open import Common.Size

-- StreamF A X i = ∀j<i. A × X j
record StreamF (A : Set) (X : Size → Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : ∀{j : Size< i} → X j
module F = StreamF

record Stream (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : ∀{j : Size< i} → Stream A j
module S = Stream


module Inlined {A T} (f : ∀ i → StreamF A T i → T i) where

  fix : ∀ i → Stream A i → StreamF A T i
  F.head (fix i s)         = S.head s
  F.tail (fix i s) {j = j} = f j (fix j (S.tail s {j = j}))


module Mutual {A T} (f : ∀ i → StreamF A T i → T i) where

 mutual

  fold : ∀ i → Stream A i → T i
  fold i s = f i (h i s)

  h : ∀ i → Stream A i → StreamF A T i
  F.head (h i s) = S.head s
  F.tail (h i s) {j = j} = fold j (S.tail s {j = j})


module Local where

  fold : ∀{A T}
    → (f : ∀ i → StreamF A T i → T i)
    → ∀ i → Stream A i → T i
  fold {A} {T} f i s = f i (h i s)
    where
      h : ∀ i → Stream A i → StreamF A T i
      F.head (h i s) = S.head s
      F.tail (h i s) {j = j} = fold f j (S.tail s {j = j})

-- Unfold for lists

-- ListF A X i = ⊤ + ∃j<i. A × X j
data ListF (A : Set) (X : Size → Set) (i : Size) : Set where
  []  : ListF A X i
  _∷_ : ∀{j : Size< i} (a : A) (xs : X j) → ListF A X i

data List (A : Set) (i : Size) : Set where
  []  : List A i
  _∷_ : ∀{j : Size< i} (a : A) (xs : List A j) → List A i

module With where

  unfold : ∀{A}{S : Size → Set}
    → (f : ∀ i → S i → ListF A S i)
    → ∀ i → S i → List A i
  unfold f i s with f i s
  ... | [] = []
  ... | _∷_ {j = j} a s' = a ∷ unfold f j s'

unfold : ∀{A}{S : Size → Set}
  → (f : ∀ i → S i → ListF A S i)
  → ∀ i → S i → List A i
unfold {A}{S} f i s = aux (f i s)
  where
    aux : ListF A S i → List A i
    aux [] = []
    aux (_∷_ {j = j} a s') = a ∷ unfold f j s'
