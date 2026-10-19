{-# OPTIONS --erasure #-}

-- Andreas, 2025-10-16, issue #4420
-- This issue was fixed in Agda 2.7.0

-- @bluescreen303 wrote:
--
-- Without `@erased ts` in `length`, the MAlonzo backend generates code that expects an additional `[AgdaAny]` argument.
--
-- The same happens for `lookup`, but marking `ts` `@erased` there breaks the function body (`length-length xs` needs `ts` in unerased form, but the result of `length-length` itself is only used for rewriting types and has no runtime representation).
--
-- As a result, this list of types `ts` sticks around at run time, where it clearly serves no purpose.

-- @UlfNorell worte:
--
-- Elaborating: rewrite/with currently refuses to abstract over erased (or irrelevant) things, but the sensible behaviour would be to do the abstraction at the appropriate modality.

-- Library

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero; suc) renaming (Nat to ℕ)
open import Agda.Builtin.Equality using (_≡_; refl)

subst : ∀{A : Set}(P : A → Set){x y : A} → x ≡ y → P x → P y
subst P refl p = p

cong : ∀{A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

data Fin : ℕ → Set where
  zero : ∀{n} → Fin (suc n)
  suc  : ∀{n} → Fin n → Fin (suc n)

List-length : {A : Set} → List A → ℕ
List-length [] = zero
List-length (x ∷ xs) = suc (List-length xs)

List-lookup : {A : Set} (xs : List A) → Fin (List-length xs) → A
List-lookup [] ()
List-lookup (x ∷ xs) zero = x
List-lookup (x ∷ xs) (suc i) = List-lookup xs i

-- Test

postulate
  A : Set
  F : A → Set

data HList : List A → Set where
  []  : HList []
  _∷_ : {t : A} {ts : List A} → F t → HList ts → HList (t ∷ ts)

length : ∀ (@erased ts : List A) → HList ts → ℕ
length _ []       = 0
length _ (_ ∷ xs) = suc (length _ xs)

-- Variant where ts is not erased in length-length

module Variant1 where

  length-length : ∀ (@ω ts) (xs : HList ts) → length ts xs ≡ List-length ts
  length-length _ []       = refl
  length-length _ (_ ∷ xs) = cong suc (length-length _ xs)

  lookup : ∀ {@erased ts : List A} (xs : HList ts) (i : Fin (length ts xs))
         → F (List-lookup ts (subst Fin (length-length ts xs) i))
  lookup (x ∷ xs) zero rewrite length-length _ xs = x
  lookup (x ∷ xs) (suc i) with lookup xs i
  ... | q rewrite length-length _ xs = q

-- Variant where ts is erased in length-length

module Variant2 where

  length-length : ∀ (@erased ts) (xs : HList ts) → length ts xs ≡ List-length ts
  length-length _ []       = refl
  length-length _ (_ ∷ xs) = cong suc (length-length _ xs)

  lookup : ∀ {@erased ts : List A} (xs : HList ts) (i : Fin (length ts xs))
         → F (List-lookup ts (subst Fin (length-length ts xs) i))
  lookup (x ∷ xs) zero rewrite length-length _ xs = x
  lookup (x ∷ xs) (suc i) with lookup xs i
  ... | q rewrite length-length _ xs = q

-- Both variants pass (since Agda 2.7.0).
