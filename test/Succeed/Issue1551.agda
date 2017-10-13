-- Andreas, 2015-06-11

{-# OPTIONS --copatterns #-}

open import Common.Size

module _ {C : Set} {R : C → Set} where

mutual
  record IO (i : Size) (A : Set) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → IO' j A

  data IO' (i : Size) (A : Set) : Set where
    act    : (c : C) (f : R c → IO i A) → IO' i A
    return : (a : A) → IO' i A

open IO

module Works where

  _>>=_ : ∀{i A B} (m : IO i A) (k : A → IO i B) → IO i B
  force (m >>= k) with force m
  force (m >>= k) {j} | act c f  = act c λ x → f x >>= k
  force (m >>= k) {j} | return a = force (k a)

_>>=_ : ∀{i A B} (m : IO i A) (k : A → IO i B) → IO i B
force (m >>= k) with force m
force (m >>= k) | act c f  = act c λ x → f x >>= k
force (m >>= k) | return a = force (k a)

-- Error WAS:
-- Too few arguments given in with-clause
-- when checking that the clause
-- force (m >>= k) with force m
-- force (m >>= k) | do c f = do c (λ x → f x >>= k)
-- force (m >>= k) | return a = force (k a)
-- has type {i : Size} {A B : Set} → IO i A → (A → IO i B) → IO i B
