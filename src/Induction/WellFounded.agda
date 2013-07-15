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

Well-founded : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Well-founded _<_ = ∀ x → Acc _<_ x

-- Well-founded induction for the subset of accessible elements:

module Some {a lt} {A : Set a} {_<_ : Rel A lt} {ℓ} where

  wfRec-builder : SubsetRecursorBuilder (Acc _<_) (WfRec _<_ {ℓ = ℓ})
  wfRec-builder P f x (acc rs) = λ y y<x →
    f y (wfRec-builder P f y (rs y y<x))

  wfRec : SubsetRecursor (Acc _<_) (WfRec _<_)
  wfRec = subsetBuild wfRec-builder

-- Well-founded induction for all elements, assuming they are all
-- accessible:

module All {a lt} {A : Set a} {_<_ : Rel A lt}
           (wf : Well-founded _<_) ℓ where

  wfRec-builder : RecursorBuilder (WfRec _<_ {ℓ = ℓ})
  wfRec-builder P f x = Some.wfRec-builder P f x (wf x)

  wfRec : Recursor (WfRec _<_)
  wfRec = build wfRec-builder

-- It might be useful to establish proofs of Acc or Well-founded using
-- combinators such as the ones below (see, for instance,
-- "Constructing Recursion Operators in Intuitionistic Type Theory" by
-- Lawrence C Paulson).

module Subrelation {a ℓ₁ ℓ₂} {A : Set a}
                   {_<₁_ : Rel A ℓ₁} {_<₂_ : Rel A ℓ₂}
                   (<₁⇒<₂ : ∀ {x y} → x <₁ y → x <₂ y) where

  accessible : Acc _<₂_ ⊆ Acc _<₁_
  accessible (acc rs) = acc (λ y y<x → accessible (rs y (<₁⇒<₂ y<x)))

  well-founded : Well-founded _<₂_ → Well-founded _<₁_
  well-founded wf = λ x → accessible (wf x)

module Inverse-image {a b ℓ} {A : Set a} {B : Set b} {_<_ : Rel B ℓ}
                     (f : A → B) where

  accessible : ∀ {x} → Acc _<_ (f x) → Acc (_<_ on f) x
  accessible (acc rs) = acc (λ y fy<fx → accessible (rs (f y) fy<fx))

  well-founded : Well-founded _<_ → Well-founded (_<_ on f)
  well-founded wf = λ x → accessible (wf (f x))

module Transitive-closure {a ℓ} {A : Set a} (_<_ : Rel A ℓ) where

  infix 4 _<⁺_

  data _<⁺_ : Rel A (a ⊔ ℓ) where
    [_]   : ∀ {x y} (x<y : x < y) → x <⁺ y
    trans : ∀ {x y z} (x<y : x <⁺ y) (y<z : y <⁺ z) → x <⁺ z

  downwards-closed : ∀ {x y} → Acc _<⁺_ y → x <⁺ y → Acc _<⁺_ x
  downwards-closed (acc rs) x<y = acc (λ z z<x → rs z (trans z<x x<y))

  mutual

    accessible : ∀ {x} → Acc _<_ x → Acc _<⁺_ x
    accessible acc-x = acc (accessible′ acc-x)

    accessible′ : ∀ {x} → Acc _<_ x → WfRec _<⁺_ (Acc _<⁺_) x
    accessible′ (acc rs) y [ y<x ]         = accessible (rs y y<x)
    accessible′ acc-x    y (trans y<z z<x) =
      downwards-closed (accessible′ acc-x _ z<x) y<z

  well-founded : Well-founded _<_ → Well-founded _<⁺_
  well-founded wf = λ x → accessible (wf x)

module Lexicographic {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b}
                     (RelA : Rel A ℓ₁)
                     (RelB : ∀ x → Rel (B x) ℓ₂) where

  data _<_ : Rel (Σ A B) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA   x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
    right : ∀ {x y₁ y₂}     (y₁<y₂ : RelB x y₁ y₂) → (x  , y₁) < (x  , y₂)

  mutual

    accessible : ∀ {x y} →
                 Acc RelA x → (∀ {x} → Well-founded (RelB x)) →
                 Acc _<_ (x , y)
    accessible accA wfB = acc (accessible′ accA (wfB _) wfB)

    accessible′ :
      ∀ {x y} →
      Acc RelA x → Acc (RelB x) y → (∀ {x} → Well-founded (RelB x)) →
      WfRec _<_ (Acc _<_) (x , y)
    accessible′ (acc rsA) _    wfB ._ (left  x′<x) = accessible (rsA _ x′<x) wfB
    accessible′ accA (acc rsB) wfB ._ (right y′<y) =
      acc (accessible′ accA (rsB _ y′<y) wfB)

  well-founded : Well-founded RelA → (∀ {x} → Well-founded (RelB x)) →
                 Well-founded _<_
  well-founded wfA wfB p = accessible (wfA (proj₁ p)) wfB
