------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a strict partial order.

module Data.Product.Relation.Lex.Strict where

open import Function
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Level
open import Relation.Nullary.Product
open import Relation.Nullary.Sum
open import Relation.Binary
open import Relation.Binary.Consequences
open import Data.Product.Relation.Pointwise.NonDependent as Pointwise
  using (Pointwise)
open import Relation.Nullary

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

------------------------------------------------------------------------
-- A lexicographic ordering over products

  ×-Lex : (_≈₁_ _<₁_ : Rel A₁ ℓ₁) → (_≤₂_ : Rel A₂ ℓ₂) → Rel (A₁ × A₂) _
  ×-Lex _≈₁_ _<₁_ _≤₂_ =
    (_<₁_ on proj₁) -⊎- (_≈₁_ on proj₁) -×- (_≤₂_ on proj₂)

------------------------------------------------------------------------
-- Some properties which are preserved by ×-Lex (under certain
-- assumptions).

  ×-reflexive : ∀ _≈₁_ _∼₁_ {_≈₂_ : Rel A₂ ℓ₂} _≤₂_ →
                _≈₂_ ⇒ _≤₂_ → (Pointwise _≈₁_ _≈₂_) ⇒ (×-Lex _≈₁_ _∼₁_ _≤₂_)
  ×-reflexive _ _ _ refl₂ = λ x≈y →
    inj₂ (proj₁ x≈y , refl₂ (proj₂ x≈y))

  ×-irreflexive : ∀ {_≈₁_ _<₁_}             → Irreflexive _≈₁_ _<₁_ →
                  ∀ {_≈₂_ _<₂_ : Rel A₂ ℓ₂} → Irreflexive _≈₂_ _<₂_ →
                  Irreflexive (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  ×-irreflexive ir₁ ir₂ x≈y (inj₁ x₁<y₁) = ir₁ (proj₁ x≈y) x₁<y₁
  ×-irreflexive ir₁ ir₂ x≈y (inj₂ x≈<y)  =
    ir₂ (proj₂ x≈y) (proj₂ x≈<y)

  ×-transitive : ∀ {_≈₁_ _<₁_} →
    IsEquivalence _≈₁_ → _<₁_ Respects₂ _≈₁_ → Transitive _<₁_ →
    ∀ {_≤₂_} → Transitive _≤₂_ → Transitive (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-transitive {_≈₁_} {_<₁_} eq₁ resp₁ trans₁ {_≤₂_} trans₂ = trans
    where
    module Eq₁ = IsEquivalence eq₁

    trans : Transitive (×-Lex _≈₁_ _<₁_ _≤₂_)
    trans (inj₁ x₁<y₁) (inj₁ y₁<z₁) = inj₁ (trans₁ x₁<y₁ y₁<z₁)
    trans (inj₁ x₁<y₁) (inj₂ y≈≤z)  =
      inj₁ (proj₁ resp₁ (proj₁ y≈≤z) x₁<y₁)
    trans (inj₂ x≈≤y)  (inj₁ y₁<z₁) =
      inj₁ (proj₂ resp₁ (Eq₁.sym $ proj₁ x≈≤y) y₁<z₁)
    trans (inj₂ x≈≤y)  (inj₂ y≈≤z)  =
      inj₂ ( Eq₁.trans (proj₁ x≈≤y) (proj₁ y≈≤z)
           , trans₂    (proj₂ x≈≤y) (proj₂ y≈≤z) )

  ×-antisymmetric : ∀ {_≈₁_ _<₁_} →
    Symmetric _≈₁_ → Irreflexive _≈₁_ _<₁_ → Asymmetric _<₁_ →
    ∀ {_≈₂_ _≤₂_ : Rel A₂ ℓ₂} → Antisymmetric _≈₂_ _≤₂_ →
    Antisymmetric (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-antisymmetric {_≈₁_} {_<₁_} sym₁ irrefl₁ asym₁
                  {_≈₂_} {_≤₂_} antisym₂ = antisym
    where
    antisym : Antisymmetric (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _<₁_ _≤₂_)
    antisym (inj₁ x₁<y₁) (inj₁ y₁<x₁) =
      ⊥-elim $ asym₁ x₁<y₁ y₁<x₁
    antisym (inj₁ x₁<y₁) (inj₂ y≈≤x)  =
      ⊥-elim $ irrefl₁ (sym₁ $ proj₁ y≈≤x) x₁<y₁
    antisym (inj₂ x≈≤y)  (inj₁ y₁<x₁) =
      ⊥-elim $ irrefl₁ (sym₁ $ proj₁ x≈≤y) y₁<x₁
    antisym (inj₂ x≈≤y)  (inj₂ y≈≤x)  =
      proj₁ x≈≤y , antisym₂ (proj₂ x≈≤y) (proj₂ y≈≤x)

  ×-asymmetric : ∀ {_≈₁_ _<₁_} →
    Symmetric _≈₁_ → _<₁_ Respects₂ _≈₁_ → Asymmetric _<₁_ →
    ∀ {_<₂_} → Asymmetric _<₂_ →
    Asymmetric (×-Lex _≈₁_ _<₁_ _<₂_)
  ×-asymmetric {_≈₁_} {_<₁_} sym₁ resp₁ asym₁ {_<₂_} asym₂ = asym
    where
    irrefl₁ : Irreflexive _≈₁_ _<₁_
    irrefl₁ = asym⟶irr resp₁ sym₁ asym₁

    asym : Asymmetric (×-Lex _≈₁_ _<₁_ _<₂_)
    asym (inj₁ x₁<y₁) (inj₁ y₁<x₁) = asym₁ x₁<y₁ y₁<x₁
    asym (inj₁ x₁<y₁) (inj₂ y≈<x)  = irrefl₁ (sym₁ $ proj₁ y≈<x) x₁<y₁
    asym (inj₂ x≈<y)  (inj₁ y₁<x₁) = irrefl₁ (sym₁ $ proj₁ x≈<y) y₁<x₁
    asym (inj₂ x≈<y)  (inj₂ y≈<x)  = asym₂ (proj₂ x≈<y) (proj₂ y≈<x)

  ×-respects₂ :
    ∀ {_≈₁_ _<₁_} → IsEquivalence _≈₁_ → _<₁_ Respects₂ _≈₁_ →
    {_≈₂_ _<₂_ : Rel A₂ ℓ₂} → _<₂_ Respects₂ _≈₂_ →
    (×-Lex _≈₁_ _<₁_ _<₂_) Respects₂ (Pointwise _≈₁_ _≈₂_)
  ×-respects₂ {_≈₁_} {_<₁_} eq₁ resp₁
              {_≈₂_} {_<₂_}     resp₂ = resp¹ , resp²
    where
    _<_ = ×-Lex _≈₁_ _<₁_ _<₂_

    open IsEquivalence eq₁ renaming (sym to sym₁; trans to trans₁)

    resp¹ : ∀ {x} → (x <_) Respects (Pointwise _≈₁_ _≈₂_)
    resp¹ y≈y' (inj₁ x₁<y₁) = inj₁ (proj₁ resp₁ (proj₁ y≈y') x₁<y₁)
    resp¹ y≈y' (inj₂ x≈<y)  =
      inj₂ ( trans₁ (proj₁ x≈<y) (proj₁ y≈y')
           , proj₁ resp₂ (proj₂ y≈y') (proj₂ x≈<y) )

    resp² : ∀ {y} → (flip _<_ y) Respects (Pointwise _≈₁_ _≈₂_)
    resp² x≈x' (inj₁ x₁<y₁) = inj₁ (proj₂ resp₁ (proj₁ x≈x') x₁<y₁)
    resp² x≈x' (inj₂ x≈<y)  =
      inj₂ ( trans₁ (sym₁ $ proj₁ x≈x') (proj₁ x≈<y)
           , proj₂ resp₂ (proj₂ x≈x') (proj₂ x≈<y) )

  ×-decidable : ∀ {_≈₁_ _<₁_} → Decidable _≈₁_ → Decidable _<₁_ →
                ∀ {_≤₂_} → Decidable _≤₂_ →
                Decidable (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-decidable dec-≈₁ dec-<₁ dec-≤₂ x y =
    dec-<₁ (proj₁ x) (proj₁ y)
      ⊎-dec
    (dec-≈₁ (proj₁ x) (proj₁ y)
       ×-dec
     dec-≤₂ (proj₂ x) (proj₂ y))

  ×-total₁ : ∀ {_≈₁_ _<₁_} → Total _<₁_ →
             ∀ {_≤₂_} → Total (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-total₁ total₁ x y with total₁ (proj₁ x) (proj₁ y)
  ... | inj₁ x₁<y₁ = inj₁ (inj₁ x₁<y₁)
  ... | inj₂ x₁>y₁ = inj₂ (inj₁ x₁>y₁)

  ×-total₂ : ∀ {_≈₁_ _<₁_} → Symmetric _≈₁_ → Trichotomous _≈₁_ _<₁_ →
             ∀ {_≤₂_} → Total _≤₂_ →
             Total (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-total₂ sym tri₁ total₂ x y with tri₁ (proj₁ x) (proj₁ y)
  ... | tri< x₁<y₁ _ _ = inj₁ (inj₁ x₁<y₁)
  ... | tri> _ _ y₁<x₁ = inj₂ (inj₁ y₁<x₁)
  ... | tri≈ _ x₁≈y₁ _ with total₂ (proj₂ x) (proj₂ y)
  ...   | inj₁ x₂≤y₂ = inj₁ (inj₂ (x₁≈y₁     , x₂≤y₂))
  ...   | inj₂ y₂≤x₂ = inj₂ (inj₂ (sym x₁≈y₁ , y₂≤x₂))

  ×-compare :
    {_≈₁_ _<₁_ : Rel A₁ ℓ₁} → Symmetric _≈₁_ → Trichotomous _≈₁_ _<₁_ →
    {_≈₂_ _<₂_ : Rel A₂ ℓ₂} → Trichotomous _≈₂_ _<₂_ →
    Trichotomous (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  ×-compare sym₁ cmp₁ cmp₂ (x₁ , x₂) (y₁ , y₂) with cmp₁ x₁ y₁
  ... | (tri< x₁<y₁ x₁≉y₁ x₁≯y₁) =
    tri< (inj₁ x₁<y₁)
         (x₁≉y₁ ∘ proj₁)
         [ x₁≯y₁ , x₁≉y₁ ∘ sym₁ ∘ proj₁ ]
  ... | (tri> x₁≮y₁ x₁≉y₁ x₁>y₁) =
    tri> [ x₁≮y₁ , x₁≉y₁ ∘ proj₁ ]
         (x₁≉y₁ ∘ proj₁)
         (inj₁ x₁>y₁)
  ... | (tri≈ x₁≮y₁ x₁≈y₁ x₁≯y₁) with cmp₂ x₂ y₂
  ...   | (tri< x₂<y₂ x₂≉y₂ x₂≯y₂) =
    tri< (inj₂ (x₁≈y₁ , x₂<y₂))
         (x₂≉y₂ ∘ proj₂)
         [ x₁≯y₁ , x₂≯y₂ ∘ proj₂ ]
  ...   | (tri> x₂≮y₂ x₂≉y₂ x₂>y₂) =
    tri> [ x₁≮y₁ , x₂≮y₂ ∘ proj₂ ]
         (x₂≉y₂ ∘ proj₂)
         (inj₂ (sym₁ x₁≈y₁ , x₂>y₂))
  ...   | (tri≈ x₂≮y₂ x₂≈y₂ x₂≯y₂) =
    tri≈ [ x₁≮y₁ , x₂≮y₂ ∘ proj₂ ]
         (x₁≈y₁ , x₂≈y₂)
         [ x₁≯y₁ , x₂≯y₂ ∘ proj₂ ]

------------------------------------------------------------------------
-- Collections of properties which are preserved by ×-Lex.

  ×-isPreorder : ∀ {_≈₁_ _∼₁_} → IsPreorder _≈₁_ _∼₁_ →
                   ∀ {_≈₂_ _∼₂_} → IsPreorder _≈₂_ _∼₂_ →
                   IsPreorder (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _∼₁_ _∼₂_)
  ×-isPreorder {_≈₁_} {_∼₁_} pre₁ {_∼₂_ = _∼₂_} pre₂ =
    record
      { isEquivalence = Pointwise.×-isEquivalence
                          (isEquivalence pre₁) (isEquivalence pre₂)
      ; reflexive     = ×-reflexive _≈₁_ _∼₁_ _∼₂_ (reflexive pre₂)
      ; trans         = ×-transitive
                          (isEquivalence pre₁) (∼-resp-≈ pre₁)
                          (trans pre₁) {_≤₂_ = _∼₂_} (trans pre₂)
      }
    where open IsPreorder

  ×-isStrictPartialOrder :
    ∀ {_≈₁_ _<₁_} → IsStrictPartialOrder _≈₁_ _<₁_ →
    ∀ {_≈₂_ _<₂_} → IsStrictPartialOrder _≈₂_ _<₂_ →
    IsStrictPartialOrder (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  ×-isStrictPartialOrder {_<₁_ = _<₁_} spo₁ {_<₂_ = _<₂_} spo₂ =
    record
      { isEquivalence = Pointwise.×-isEquivalence
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = ×-irreflexive {_<₁_ = _<₁_} (irrefl spo₁)
                                      {_<₂_ = _<₂_} (irrefl spo₂)
      ; trans         = ×-transitive
                          {_<₁_ = _<₁_} (isEquivalence spo₁)
                                        (<-resp-≈ spo₁) (trans spo₁)
                          {_≤₂_ = _<₂_} (trans spo₂)
      ; <-resp-≈      = ×-respects₂ (isEquivalence spo₁)
                                      (<-resp-≈ spo₁)
                                      (<-resp-≈ spo₂)
      }
    where open IsStrictPartialOrder

  ×-isStrictTotalOrder :
    ∀ {_≈₁_ _<₁_} → IsStrictTotalOrder _≈₁_ _<₁_ →
    ∀ {_≈₂_ _<₂_} → IsStrictTotalOrder _≈₂_ _<₂_ →
    IsStrictTotalOrder (Pointwise _≈₁_ _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  ×-isStrictTotalOrder {_<₁_ = _<₁_} spo₁ {_<₂_ = _<₂_} spo₂ =
    record
      { isEquivalence = Pointwise.×-isEquivalence
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; trans         = ×-transitive
                          {_<₁_ = _<₁_} (isEquivalence spo₁)
                                        (<-resp-≈ spo₁) (trans spo₁)
                          {_≤₂_ = _<₂_} (trans spo₂)
      ; compare       = ×-compare (Eq.sym spo₁) (compare spo₁)
                                                (compare spo₂)
      }
    where open IsStrictTotalOrder

------------------------------------------------------------------------
-- "Packages" can also be combined.

module _ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} where

  ×-preorder : Preorder ℓ₁ ℓ₂ _ → Preorder ℓ₃ ℓ₄ _ → Preorder _ _ _
  ×-preorder p₁ p₂ = record
    { isPreorder = ×-isPreorder (isPreorder p₁) (isPreorder p₂)
    } where open Preorder

  ×-strictPartialOrder :
    StrictPartialOrder ℓ₁ ℓ₂ _ → StrictPartialOrder ℓ₃ ℓ₄ _ →
    StrictPartialOrder _ _ _
  ×-strictPartialOrder s₁ s₂ = record
    { isStrictPartialOrder = ×-isStrictPartialOrder
        (isStrictPartialOrder s₁) (isStrictPartialOrder s₂)
    } where open StrictPartialOrder

  ×-strictTotalOrder :
    StrictTotalOrder ℓ₁ ℓ₂ _ → StrictTotalOrder ℓ₃ ℓ₄ _ →
    StrictTotalOrder _ _ _
  ×-strictTotalOrder s₁ s₂ = record
    { isStrictTotalOrder = ×-isStrictTotalOrder
        (isStrictTotalOrder s₁) (isStrictTotalOrder s₂)
    } where open StrictTotalOrder

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

_×-irreflexive_          = ×-irreflexive
_×-isPreorder_           = ×-isPreorder
_×-isStrictPartialOrder_ = ×-isStrictPartialOrder
_×-isStrictTotalOrder_   = ×-isStrictTotalOrder
_×-preorder_             = ×-preorder
_×-strictPartialOrder_   = ×-strictPartialOrder
_×-strictTotalOrder_     = ×-strictTotalOrder

×-≈-respects₂            = ×-respects₂
