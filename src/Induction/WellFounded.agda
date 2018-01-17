------------------------------------------------------------------------
-- The Agda standard library
--
-- Well-founded induction
------------------------------------------------------------------------

open import Relation.Binary

module Induction.WellFounded where

open import Data.Product
open import Function
open import Induction
open import Level
open import Relation.Unary

-- When using well-founded recursion you can recurse arbitrarily, as
-- long as the arguments become smaller, and "smaller" is
-- well-founded.

WfRec : ∀ {a r} {A : Set a} → Rel A r → ∀ {ℓ} → RecStruct A ℓ _
WfRec _<_ P x = ∀ y → y < x → P y

-- The accessibility predicate: x is accessible if everything which is
-- smaller than x is also accessible (inductively).

data Acc {a ℓ} {A : Set a} (_<_ : Rel A ℓ) (x : A) : Set (a ⊔ ℓ) where
  acc : (rs : WfRec _<_ (Acc _<_) x) → Acc _<_ x

-- The accessibility predicate encodes what it means to be
-- well-founded; if all elements are accessible, then _<_ is
-- well-founded.

WellFounded : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
WellFounded _<_ = ∀ x → Acc _<_ x

-- DEPRECATED - please use WellFounded instead
Well-founded = WellFounded

------------------------------------------------------------------------
-- Well-founded induction for the subset of accessible elements:

module Some {a lt} {A : Set a} {_<_ : Rel A lt} {ℓ} where

  wfRecBuilder : SubsetRecursorBuilder (Acc _<_) (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x (acc rs) = λ y y<x →
    f y (wfRecBuilder P f y (rs y y<x))

  wfRec : SubsetRecursor (Acc _<_) (WfRec _<_)
  wfRec = subsetBuild wfRecBuilder

  -- DEPRECATED - please use WellFounded instead
  wfRec-builder = wfRecBuilder

------------------------------------------------------------------------
-- Well-founded induction for all elements, assuming they are all
-- accessible:

module All {a lt} {A : Set a} {_<_ : Rel A lt}
           (wf : WellFounded _<_) ℓ where

  wfRecBuilder : RecursorBuilder (WfRec _<_ {ℓ = ℓ})
  wfRecBuilder P f x = Some.wfRecBuilder P f x (wf x)

  wfRec : Recursor (WfRec _<_)
  wfRec = build wfRecBuilder

  -- DEPRECATED - please use WellFounded instead
  wfRec-builder = wfRecBuilder

------------------------------------------------------------------------
-- It might be useful to establish proofs of Acc or Well-founded using
-- combinators such as the ones below (see, for instance,
-- "Constructing Recursion Operators in Intuitionistic Type Theory" by
-- Lawrence C Paulson).

module Subrelation {a ℓ₁ ℓ₂} {A : Set a}
                   {_<₁_ : Rel A ℓ₁} {_<₂_ : Rel A ℓ₂}
                   (<₁⇒<₂ : ∀ {x y} → x <₁ y → x <₂ y) where

  accessible : Acc _<₂_ ⊆ Acc _<₁_
  accessible (acc rs) = acc (λ y y<x → accessible (rs y (<₁⇒<₂ y<x)))

  wellFounded : WellFounded _<₂_ → WellFounded _<₁_
  wellFounded wf = λ x → accessible (wf x)

  -- DEPRECATED - please use wellFounded instead
  well-founded = wellFounded

module Inverse-image {a b ℓ} {A : Set a} {B : Set b} {_<_ : Rel B ℓ}
                     (f : A → B) where

  accessible : ∀ {x} → Acc _<_ (f x) → Acc (_<_ on f) x
  accessible (acc rs) = acc (λ y fy<fx → accessible (rs (f y) fy<fx))

  wellFounded : WellFounded _<_ → WellFounded (_<_ on f)
  wellFounded wf = λ x → accessible (wf (f x))

  -- DEPRECATED - please use wellFounded instead
  well-founded = wellFounded

module Transitive-closure {a ℓ} {A : Set a} (_<_ : Rel A ℓ) where

  infix 4 _<⁺_

  data _<⁺_ : Rel A (a ⊔ ℓ) where
    [_]   : ∀ {x y} (x<y : x < y) → x <⁺ y
    trans : ∀ {x y z} (x<y : x <⁺ y) (y<z : y <⁺ z) → x <⁺ z

  downwardsClosed : ∀ {x y} → Acc _<⁺_ y → x <⁺ y → Acc _<⁺_ x
  downwardsClosed (acc rs) x<y = acc (λ z z<x → rs z (trans z<x x<y))

  mutual

    accessible : ∀ {x} → Acc _<_ x → Acc _<⁺_ x
    accessible acc-x = acc (accessible′ acc-x)

    accessible′ : ∀ {x} → Acc _<_ x → WfRec _<⁺_ (Acc _<⁺_) x
    accessible′ (acc rs) y [ y<x ]         = accessible (rs y y<x)
    accessible′ acc-x    y (trans y<z z<x) =
      downwardsClosed (accessible′ acc-x _ z<x) y<z

  wellFounded : WellFounded _<_ → WellFounded _<⁺_
  wellFounded wf = λ x → accessible (wf x)

  -- DEPRECATED - please use wellFounded and downwardsClosed instead
  downwards-closed = downwardsClosed
  well-founded     = wellFounded

module Lexicographic {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b}
                     (RelA : Rel A ℓ₁)
                     (RelB : ∀ x → Rel (B x) ℓ₂) where

  data _<_ : Rel (Σ A B) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA   x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
    right : ∀ {x y₁ y₂}     (y₁<y₂ : RelB x y₁ y₂) → (x  , y₁) < (x  , y₂)

  mutual

    accessible : ∀ {x y} →
                 Acc RelA x → (∀ {x} → WellFounded (RelB x)) →
                 Acc _<_ (x , y)
    accessible accA wfB = acc (accessible′ accA (wfB _) wfB)

    accessible′ :
      ∀ {x y} →
      Acc RelA x → Acc (RelB x) y → (∀ {x} → WellFounded (RelB x)) →
      WfRec _<_ (Acc _<_) (x , y)
    accessible′ (acc rsA) _    wfB ._ (left  x′<x) = accessible (rsA _ x′<x) wfB
    accessible′ accA (acc rsB) wfB ._ (right y′<y) =
      acc (accessible′ accA (rsB _ y′<y) wfB)

  wellFounded : WellFounded RelA → (∀ {x} → WellFounded (RelB x)) →
                WellFounded _<_
  wellFounded wfA wfB p = accessible (wfA (proj₁ p)) wfB

  -- DEPRECATED - please use wellFounded instead
  well-founded = wellFounded
