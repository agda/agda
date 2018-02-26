------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

module Data.List.Relation.Lex.Core where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Function using (_∘_; flip; id)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_)
open import Level using (_⊔_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary
open import Data.List.Relation.Pointwise
   using (Pointwise; []; _∷_; head; tail)

-- The lexicographic ordering itself can be either strict or non-strict,
-- depending on whether type P is inhabited.

data Lex {a ℓ₁ ℓ₂} {A : Set a} (P : Set)
         (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) : Rel (List A) (ℓ₁ ⊔ ℓ₂) where
  base : P                             → Lex P _≈_ _≺_ []       []
  halt : ∀ {y ys}                      → Lex P _≈_ _≺_ []       (y ∷ ys)
  this : ∀ {x xs y ys} (x≺y : x ≺ y)   → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)
  next : ∀ {x xs y ys} (x≈y : x ≈ y)
         (xs<ys : Lex P _≈_ _≺_ xs ys) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)

-- Properties

module _ {a ℓ₁ ℓ₂} {A : Set a} {P : Set}
         {_≈_ : Rel A ℓ₁} {_≺_ : Rel A ℓ₂} where

  private
    _≋_ = Pointwise _≈_
    _<_ = Lex P _≈_ _≺_

  ¬≤-this : ∀ {x y xs ys} → ¬ (x ≈ y) → ¬ (x ≺ y) →
            ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-this x≉y x≮y (this x≺y)       = x≮y x≺y
  ¬≤-this x≉y x≮y (next x≈y xs<ys) = x≉y x≈y

  ¬≤-next : ∀ {x y xs ys} → ¬ x ≺ y → ¬ xs < ys →
            ¬ (x ∷ xs) < (y ∷ ys)
  ¬≤-next x≮y xs≮ys (this x≺y)     = x≮y x≺y
  ¬≤-next x≮y xs≮ys (next _ xs<ys) = xs≮ys xs<ys

  transitive : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → Transitive _≺_ →
               Transitive _<_
  transitive eq resp tr = trans
    where
    trans : Transitive (Lex P _≈_ _≺_)
    trans (base p)         (base _)         = base p
    trans (base y)         halt             = halt
    trans halt             (this y≺z)       = halt
    trans halt             (next y≈z ys<zs) = halt
    trans (this x≺y)       (this y≺z)       = this (tr x≺y y≺z)
    trans (this x≺y)       (next y≈z ys<zs) = this (proj₁ resp y≈z x≺y)
    trans (next x≈y xs<ys) (this y≺z)       =
      this (proj₂ resp (IsEquivalence.sym eq x≈y) y≺z)
    trans (next x≈y xs<ys) (next y≈z ys<zs) =
      next (IsEquivalence.trans eq x≈y y≈z) (trans xs<ys ys<zs)

  antisymmetric : Symmetric _≈_ → Irreflexive _≈_ _≺_ →
                  Asymmetric _≺_ → Antisymmetric _≋_ _<_
  antisymmetric sym ir asym = as
    where
    as : Antisymmetric _≋_ _<_
    as (base _)         (base _)         = []
    as halt             ()
    as (this x≺y)       (this y≺x)       = ⊥-elim (asym x≺y y≺x)
    as (this x≺y)       (next y≈x ys<xs) = ⊥-elim (ir (sym y≈x) x≺y)
    as (next x≈y xs<ys) (this y≺x)       = ⊥-elim (ir (sym x≈y) y≺x)
    as (next x≈y xs<ys) (next y≈x ys<xs) = x≈y ∷ as xs<ys ys<xs

  respects₂ : IsEquivalence _≈_ → _≺_ Respects₂ _≈_ → _<_ Respects₂ _≋_
  respects₂ eq (resp₁ , resp₂) = resp¹ , resp²
    where
    open IsEquivalence eq using (sym; trans)
    resp¹ : ∀ {xs} → Lex P _≈_ _≺_ xs Respects _≋_
    resp¹ []            xs<[]            = xs<[]
    resp¹ (_   ∷ _)     halt             = halt
    resp¹ (x≈y ∷ _)     (this z≺x)       = this (resp₁ x≈y z≺x)
    resp¹ (x≈y ∷ xs≋ys) (next z≈x zs<xs) =
      next (trans z≈x x≈y) (resp¹ xs≋ys zs<xs)

    resp² : ∀ {ys} → flip (Lex P _≈_ _≺_) ys Respects _≋_
    resp² []            []<ys            = []<ys
    resp² (x≈z ∷ _)     (this x≺y)       = this (resp₂ x≈z x≺y)
    resp² (x≈z ∷ xs≋zs) (next x≈y xs<ys) =
      next (trans (sym x≈z) x≈y) (resp² xs≋zs xs<ys)

  decidable : Dec P → Decidable _≈_ → Decidable _≺_ → Decidable _<_
  decidable (yes p) dec-≈ dec-≺ []       []       = yes (base p)
  decidable (no ¬p) dec-≈ dec-≺ []       []       = no λ{(base p) → ¬p p}
  decidable dec-P   dec-≈ dec-≺ []       (y ∷ ys) = yes halt
  decidable dec-P   dec-≈ dec-≺ (x ∷ xs) []       = no λ()
  decidable dec-P   dec-≈ dec-≺ (x ∷ xs) (y ∷ ys) with dec-≺ x y
  ... | yes x≺y = yes (this x≺y)
  ... | no x≮y with dec-≈ x y
  ...   | no x≉y = no (¬≤-this x≉y x≮y)
  ...   | yes x≈y with decidable dec-P dec-≈ dec-≺ xs ys
  ...     | yes xs<ys = yes (next x≈y xs<ys)
  ...     | no  xs≮ys = no (¬≤-next x≮y xs≮ys)
