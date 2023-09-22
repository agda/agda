-- Andreas, 2015-06-11, issue #1551

{-# OPTIONS --copatterns --sized-types #-}

module _ where

open import Agda.Builtin.Size

module IOTree {C : Set} {R : C → Set} where

  mutual
    record IO (i : Size) (A : Set) : Set where
      coinductive
      constructor delay
      field
        force : {j : Size< i} → IO' j A

    data IO' (i : Size) (A : Set) : Set where
      act     : (c : C) (f : R c → IO i A) → IO' i A
      return' : (a : A) → IO' i A

  open IO public

  return : ∀{i A} (a : A) → IO i A
  return a .force = return' a

  module Works where

    _>>=_ : ∀{i A B} (m : IO i A) (k : A → IO i B) → IO i B
    force (m >>= k) with force m
    force (m >>= k) {j} | act c f   = act c λ x → f x >>= k
    force (m >>= k) {j} | return' a = force (k a)

  _>>=_ : ∀{i A B} (m : IO i A) (k : A → IO i B) → IO i B
  force (m >>= k) with force m
  force (m >>= k) | act c f  = act c λ x → f x >>= k
  force (m >>= k) | return' a = force (k a)

  -- Error WAS:
  -- Too few arguments given in with-clause
  -- when checking that the clause
  -- force (m >>= k) with force m
  -- force (m >>= k) | do c f = do c (λ x → f x >>= k)
  -- force (m >>= k) | return a = force (k a)
  -- has type {i : Size} {A B : Set} → IO i A → (A → IO i B) → IO i B


-- Andreas, 2023-06-21, re issue #6660

data ⊥ : Set where
record ⊤ : Set where

open IOTree {R = λ (_ : ⊤) → ⊤}

tick : ∀ {i : Size} → IO (↑ i) ⊤
tick .force = act _ λ _ → return _

tick' : ∀ {i A} → IO i A → IO' i A
tick' cont = act _ λ _ → cont

forever : ∀ {i : Size} → IO i ⊥
forever .force = tick' forever

-- Can't write this:
--
-- forever : ∀ {i : Size} → IO i ⊥
-- forever = do
--   _ ← tick
--   forever

-- Even this is not possible yet:

-- {-# INLINE delay #-}

-- forever' : ∀ {i : Size} → IO i ⊥
-- forever' = delay (tick' forever)

-- IO' _i_79 _A_80 !=< {j : Size< i} → IO' j ⊥
-- when checking that the inferred type of an application
--   IO' _i_79 _A_80
-- matches the expected type
--   {j : Size< i} → IO' j ⊥
