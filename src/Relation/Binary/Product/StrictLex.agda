------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic products of binary relations
------------------------------------------------------------------------

-- The definition of lexicographic product used here is suitable if
-- the left-hand relation is a strict partial order.

module Relation.Binary.Product.StrictLex where

open import Function
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Level
open import Relation.Nullary.Product
open import Relation.Nullary.Sum
open import Relation.Binary
open import Relation.Binary.Consequences
open import Relation.Binary.Product.Pointwise as Pointwise
  using (_×-Rel_)
open import Relation.Nullary

module _ {a₁ a₂ ℓ₁ ℓ₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  ×-Lex : (_≈₁_ _<₁_ : Rel A₁ ℓ₁) → (_≤₂_ : Rel A₂ ℓ₂) → Rel (A₁ × A₂) _
  ×-Lex _≈₁_ _<₁_ _≤₂_ =
    (_<₁_ on proj₁) -⊎- (_≈₁_ on proj₁) -×- (_≤₂_ on proj₂)

  -- Some properties which are preserved by ×-Lex (under certain
  -- assumptions).

  ×-reflexive : ∀ _≈₁_ _∼₁_ {_≈₂_ : Rel A₂ ℓ₂} _≤₂_ →
                _≈₂_ ⇒ _≤₂_ → (_≈₁_ ×-Rel _≈₂_) ⇒ (×-Lex _≈₁_ _∼₁_ _≤₂_)
  ×-reflexive _ _ _ refl₂ = λ x≈y →
    inj₂ (proj₁ x≈y , refl₂ (proj₂ x≈y))

  _×-irreflexive_ : ∀ {_≈₁_ _<₁_}             → Irreflexive _≈₁_ _<₁_ →
                    ∀ {_≈₂_ _<₂_ : Rel A₂ ℓ₂} → Irreflexive _≈₂_ _<₂_ →
                    Irreflexive (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  (ir₁ ×-irreflexive ir₂) x≈y (inj₁ x₁<y₁) = ir₁ (proj₁ x≈y) x₁<y₁
  (ir₁ ×-irreflexive ir₂) x≈y (inj₂ x≈<y)  =
    ir₂ (proj₂ x≈y) (proj₂ x≈<y)

  ×-transitive :
    ∀ {_≈₁_ _<₁_} →
    IsEquivalence _≈₁_ → _<₁_ Respects₂ _≈₁_ → Transitive _<₁_ →
    ∀ {_≤₂_} →
    Transitive _≤₂_ →
    Transitive (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-transitive {_≈₁_} {_<₁_} eq₁ resp₁ trans₁
               {_≤₂_} trans₂ = trans
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

  ×-antisymmetric :
    ∀ {_≈₁_ _<₁_} →
    Symmetric _≈₁_ → Irreflexive _≈₁_ _<₁_ → Asymmetric _<₁_ →
    ∀ {_≈₂_ _≤₂_ : Rel A₂ ℓ₂} →
    Antisymmetric _≈₂_ _≤₂_ →
    Antisymmetric (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _<₁_ _≤₂_)
  ×-antisymmetric {_≈₁_} {_<₁_} sym₁ irrefl₁ asym₁
                  {_≈₂_} {_≤₂_} antisym₂ = antisym
    where
    antisym : Antisymmetric (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _<₁_ _≤₂_)
    antisym (inj₁ x₁<y₁) (inj₁ y₁<x₁) =
      ⊥-elim $ asym₁ x₁<y₁ y₁<x₁
    antisym (inj₁ x₁<y₁) (inj₂ y≈≤x)  =
      ⊥-elim $ irrefl₁ (sym₁ $ proj₁ y≈≤x) x₁<y₁
    antisym (inj₂ x≈≤y)  (inj₁ y₁<x₁) =
      ⊥-elim $ irrefl₁ (sym₁ $ proj₁ x≈≤y) y₁<x₁
    antisym (inj₂ x≈≤y)  (inj₂ y≈≤x)  =
      proj₁ x≈≤y , antisym₂ (proj₂ x≈≤y) (proj₂ y≈≤x)

  ×-asymmetric :
    ∀ {_≈₁_ _<₁_} →
    Symmetric _≈₁_ → _<₁_ Respects₂ _≈₁_ → Asymmetric _<₁_ →
    ∀ {_<₂_} →
    Asymmetric _<₂_ →
    Asymmetric (×-Lex _≈₁_ _<₁_ _<₂_)
  ×-asymmetric {_≈₁_} {_<₁_} sym₁ resp₁ asym₁
               {_<₂_} asym₂ = asym
    where
    irrefl₁ : Irreflexive _≈₁_ _<₁_
    irrefl₁ = asym⟶irr resp₁ sym₁ asym₁

    asym : Asymmetric (×-Lex _≈₁_ _<₁_ _<₂_)
    asym (inj₁ x₁<y₁) (inj₁ y₁<x₁) = asym₁ x₁<y₁ y₁<x₁
    asym (inj₁ x₁<y₁) (inj₂ y≈<x)  = irrefl₁ (sym₁ $ proj₁ y≈<x) x₁<y₁
    asym (inj₂ x≈<y)  (inj₁ y₁<x₁) = irrefl₁ (sym₁ $ proj₁ x≈<y) y₁<x₁
    asym (inj₂ x≈<y)  (inj₂ y≈<x)  = asym₂ (proj₂ x≈<y) (proj₂ y≈<x)

  ×-≈-respects₂ :
    ∀ {_≈₁_ _<₁_} → IsEquivalence _≈₁_ → _<₁_ Respects₂ _≈₁_ →
    {_≈₂_ _<₂_ : Rel A₂ ℓ₂} → _<₂_ Respects₂ _≈₂_ →
    (×-Lex _≈₁_ _<₁_ _<₂_) Respects₂ (_≈₁_ ×-Rel _≈₂_)
  ×-≈-respects₂ {_≈₁_} {_<₁_} eq₁ resp₁
                {_≈₂_} {_<₂_}     resp₂ = resp¹ , resp²
    where
    _<_ = ×-Lex _≈₁_ _<₁_ _<₂_

    open IsEquivalence eq₁ renaming (sym to sym₁; trans to trans₁)

    resp¹ : ∀ {x} → (x <_) Respects (_≈₁_ ×-Rel _≈₂_)
    resp¹ y≈y' (inj₁ x₁<y₁) = inj₁ (proj₁ resp₁ (proj₁ y≈y') x₁<y₁)
    resp¹ y≈y' (inj₂ x≈<y)  =
      inj₂ ( trans₁ (proj₁ x≈<y) (proj₁ y≈y')
           , proj₁ resp₂ (proj₂ y≈y') (proj₂ x≈<y) )

    resp² : ∀ {y} → (flip _<_ y) Respects (_≈₁_ ×-Rel _≈₂_)
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
    Trichotomous (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  ×-compare {_≈₁_} {_<₁_} sym₁ compare₁ {_≈₂_} {_<₂_} compare₂ = cmp
    where
    cmp″ : ∀ {x₁ y₁ x₂ y₂} →
           ¬ (x₁ <₁ y₁) → x₁ ≈₁ y₁ → ¬ (y₁ <₁ x₁) →
           Tri (x₂ <₂ y₂) (x₂ ≈₂ y₂) (y₂ <₂ x₂) →
           Tri (×-Lex _≈₁_ _<₁_ _<₂_ (x₁ , x₂) (y₁ , y₂))
               ((_≈₁_ ×-Rel _≈₂_) (x₁ , x₂) (y₁ , y₂))
               (×-Lex _≈₁_ _<₁_ _<₂_ (y₁ , y₂) (x₁ , x₂))
    cmp″ x₁≮y₁ x₁≈y₁ x₁≯y₁ (tri< x₂<y₂ x₂≉y₂ x₂≯y₂) =
      tri< (inj₂ (x₁≈y₁ , x₂<y₂))
           (x₂≉y₂ ∘ proj₂)
           [ x₁≯y₁ , x₂≯y₂ ∘ proj₂ ]
    cmp″ x₁≮y₁ x₁≈y₁ x₁≯y₁ (tri> x₂≮y₂ x₂≉y₂ x₂>y₂) =
      tri> [ x₁≮y₁ , x₂≮y₂ ∘ proj₂ ]
           (x₂≉y₂ ∘ proj₂)
           (inj₂ (sym₁ x₁≈y₁ , x₂>y₂))
    cmp″ x₁≮y₁ x₁≈y₁ x₁≯y₁ (tri≈ x₂≮y₂ x₂≈y₂ x₂≯y₂) =
      tri≈ [ x₁≮y₁ , x₂≮y₂ ∘ proj₂ ]
           (x₁≈y₁ , x₂≈y₂)
           [ x₁≯y₁ , x₂≯y₂ ∘ proj₂ ]

    cmp′ : ∀ {x₁ y₁} → Tri (x₁ <₁ y₁) (x₁ ≈₁ y₁) (y₁ <₁ x₁) →
           ∀ x₂ y₂ →
           Tri (×-Lex _≈₁_ _<₁_ _<₂_ (x₁ , x₂) (y₁ , y₂))
               ((_≈₁_ ×-Rel _≈₂_) (x₁ , x₂) (y₁ , y₂))
               (×-Lex _≈₁_ _<₁_ _<₂_ (y₁ , y₂) (x₁ , x₂))
    cmp′ (tri< x₁<y₁ x₁≉y₁ x₁≯y₁) x₂ y₂ =
      tri< (inj₁ x₁<y₁) (x₁≉y₁ ∘ proj₁) [ x₁≯y₁ , x₁≉y₁ ∘ sym₁ ∘ proj₁ ]
    cmp′ (tri> x₁≮y₁ x₁≉y₁ x₁>y₁) x₂ y₂ =
      tri> [ x₁≮y₁ , x₁≉y₁ ∘ proj₁ ] (x₁≉y₁ ∘ proj₁) (inj₁ x₁>y₁)
    cmp′ (tri≈ x₁≮y₁ x₁≈y₁ x₁≯y₁) x₂ y₂ =
      cmp″ x₁≮y₁ x₁≈y₁ x₁≯y₁ (compare₂ x₂ y₂)

    cmp : Trichotomous (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
    cmp (x₁ , x₂) (y₁ , y₂) = cmp′ (compare₁ x₁ y₁) x₂ y₂

  -- Some collections of properties which are preserved by ×-Lex.

  _×-isPreorder_ : ∀ {_≈₁_ _∼₁_} → IsPreorder _≈₁_ _∼₁_ →
                   ∀ {_≈₂_ _∼₂_} → IsPreorder _≈₂_ _∼₂_ →
                   IsPreorder (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _∼₁_ _∼₂_)
  _×-isPreorder_ {_≈₁_} {_∼₁_} pre₁ {_∼₂_ = _∼₂_} pre₂ =
    record
      { isEquivalence = Pointwise._×-isEquivalence_
                          (isEquivalence pre₁) (isEquivalence pre₂)
      ; reflexive     = ×-reflexive _≈₁_ _∼₁_ _∼₂_ (reflexive pre₂)
      ; trans         = ×-transitive
                          (isEquivalence pre₁) (∼-resp-≈ pre₁)
                          (trans pre₁) {_≤₂_ = _∼₂_} (trans pre₂)
      }
    where open IsPreorder

  _×-isStrictPartialOrder_ :
    ∀ {_≈₁_ _<₁_} → IsStrictPartialOrder _≈₁_ _<₁_ →
    ∀ {_≈₂_ _<₂_} → IsStrictPartialOrder _≈₂_ _<₂_ →
    IsStrictPartialOrder (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  _×-isStrictPartialOrder_ {_<₁_ = _<₁_} spo₁ {_<₂_ = _<₂_} spo₂ =
    record
      { isEquivalence = Pointwise._×-isEquivalence_
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = _×-irreflexive_ {_<₁_ = _<₁_} (irrefl spo₁)
                                        {_<₂_ = _<₂_} (irrefl spo₂)
      ; trans         = ×-transitive
                          {_<₁_ = _<₁_} (isEquivalence spo₁)
                                        (<-resp-≈ spo₁) (trans spo₁)
                          {_≤₂_ = _<₂_} (trans spo₂)
      ; <-resp-≈      = ×-≈-respects₂ (isEquivalence spo₁)
                                      (<-resp-≈ spo₁)
                                      (<-resp-≈ spo₂)
      }
    where open IsStrictPartialOrder

  _×-isStrictTotalOrder_ :
    ∀ {_≈₁_ _<₁_} → IsStrictTotalOrder _≈₁_ _<₁_ →
    ∀ {_≈₂_ _<₂_} → IsStrictTotalOrder _≈₂_ _<₂_ →
    IsStrictTotalOrder (_≈₁_ ×-Rel _≈₂_) (×-Lex _≈₁_ _<₁_ _<₂_)
  _×-isStrictTotalOrder_ {_<₁_ = _<₁_} spo₁ {_<₂_ = _<₂_} spo₂ =
    record
      { isEquivalence = Pointwise._×-isEquivalence_
                          (isEquivalence spo₁) (isEquivalence spo₂)
      ; trans         = ×-transitive
                          {_<₁_ = _<₁_} (isEquivalence spo₁)
                                        (<-resp-≈ spo₁) (trans spo₁)
                          {_≤₂_ = _<₂_} (trans spo₂)
      ; compare       = ×-compare (Eq.sym spo₁) (compare spo₁)
                                                (compare spo₂)
      }
    where open IsStrictTotalOrder

-- "Packages" (e.g. preorders) can also be combined.

_×-preorder_ :
  ∀ {p₁ p₂ p₃ p₄} →
  Preorder p₁ p₂ _ → Preorder p₃ p₄ _ → Preorder _ _ _
p₁ ×-preorder p₂ = record
  { isPreorder = isPreorder p₁ ×-isPreorder isPreorder p₂
  } where open Preorder

_×-strictPartialOrder_ :
  ∀ {s₁ s₂ s₃ s₄} →
  StrictPartialOrder s₁ s₂ _ → StrictPartialOrder s₃ s₄ _ →
  StrictPartialOrder _ _ _
s₁ ×-strictPartialOrder s₂ = record
  { isStrictPartialOrder = isStrictPartialOrder s₁
                             ×-isStrictPartialOrder
                           isStrictPartialOrder s₂
  } where open StrictPartialOrder

_×-strictTotalOrder_ :
  ∀ {s₁ s₂ s₃ s₄} →
  StrictTotalOrder s₁ s₂ _ → StrictTotalOrder s₃ s₄ _ →
  StrictTotalOrder _ _ _
s₁ ×-strictTotalOrder s₂ = record
  { isStrictTotalOrder = isStrictTotalOrder s₁
                           ×-isStrictTotalOrder
                         isStrictTotalOrder s₂
  } where open StrictTotalOrder
