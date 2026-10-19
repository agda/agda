-- Andreas, 2025-10-22, issue #8150.
-- Produced helper function has the wrong argument order.

-- {-# OPTIONS -v interaction.helper:30 #-}

open import Agda.Builtin.List

variable
  A : Set
  x y : A
  xs ys ys' zs : List A

data _∈_ (x : A) : List A → Set where
  here : x ∈ (x ∷ xs)
  there : (i : x ∈ xs) → x ∈ (y ∷ xs)

variable
  i : x ∈ xs

delete : (xs : List A) (i : x ∈ xs) → List A
delete (._∷_ x xs) here = xs
delete (._∷_ x xs) (there i)   = x ∷ delete xs i

data SuperBag {A : Set} : (xs ys : List A) → Set where
  [] : SuperBag xs []
  _∷_ : (i : y ∈ xs) (sb : SuperBag (delete xs i) ys) → SuperBag xs (y ∷ ys)

Reindex : (xs ys : List A) → Set
Reindex xs ys = ∀{x} → x ∈ xs → x ∈ ys

reindex-delete : (i : x ∈ xs) → Reindex (delete xs i) xs
reindex-delete here j         = there j
reindex-delete (there i) here = here
reindex-delete (there i) (there j)   = there (reindex-delete i j)

reindex : SuperBag xs ys → Reindex ys xs
reindex (i ∷ sb) here = i
reindex (i ∷ sb) (there j) = reindex-delete i (reindex sb j)

SuperBag-refl : SuperBag xs xs
SuperBag-refl {xs = []}     = []
SuperBag-refl {xs = x ∷ xs} = here ∷ SuperBag-refl {xs = xs}

SuperBag-trans : SuperBag xs ys → SuperBag ys zs → SuperBag xs zs
SuperBag-trans sb [] = []
SuperBag-trans sb (i ∷ sb') = (reindex sb i) ∷ {!SuperBag-delete i sb sb'!}  -- C-c C-h

-- Expected: arguments to helper SuperBag-delete are in right order
-- SuperBag-delete : (i : y ∈ ys) (sb : SuperBag xs ys) →
--                   SuperBag (delete ys i) ys → SuperBag (delete xs (reindex sb i)) ys
-- (For now, the names are still incorrect, the last two ys should be ys' or so.)
