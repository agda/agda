------------------------------------------------------------------------
-- Pointwise "dependent products" of binary relations
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Sigma.Pointwise where

open import Data.Product as Prod
open import Level
open import Function
import Function.Equality as F
open import Function.Equivalence as Eq
  using (Equivalent; _⇔_; module Equivalent)
  renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse as Inv
  using (Inverse; _⇿_; module Inverse)
  renaming (_∘_ to _⟪∘⟫_)
open import Function.LeftInverse
  using (_LeftInverseOf_; _RightInverseOf_)
import Relation.Binary as B
open import Relation.Binary.Indexed as I using (_at_)
import Relation.Binary.HeterogeneousEquality as H
import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------
-- Pointwise products

infixr 4 _,_

data REL {a₁ a₂ b₁ b₂ ℓ₁ ℓ₂}
         {A₁ : Set a₁} (B₁ : A₁ → Set b₁)
         {A₂ : Set a₂} (B₂ : A₂ → Set b₂)
         (_R₁_ : B.REL A₁ A₂ ℓ₁) (_R₂_ : I.REL B₁ B₂ ℓ₂) :
         B.REL (Σ A₁ B₁) (Σ A₂ B₂) (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  _,_ : {x₁ : A₁} {y₁ : B₁ x₁} {x₂ : A₂} {y₂ : B₂ x₂}
        (x₁Rx₂ : x₁ R₁ x₂) (y₁Ry₂ : y₁ R₂ y₂) →
        REL B₁ B₂ _R₁_ _R₂_ (x₁ , y₁) (x₂ , y₂)

Rel : ∀ {a b ℓ₁ ℓ₂} {A : Set a} (B : A → Set b)
      (_R₁_ : B.Rel A ℓ₁) (_R₂_ : I.Rel B ℓ₂) → B.Rel (Σ A B) _
Rel B = REL B B

------------------------------------------------------------------------
-- Rel preserves many properties

private
 module Dummy {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b}
              {R₁ : B.Rel A ℓ₁} {R₂ : I.Rel B ℓ₂} where

  refl : B.Reflexive R₁ → I.Reflexive B R₂ →
         B.Reflexive (Rel B R₁ R₂)
  refl refl₁ refl₂ {x = (x , y)} = (refl₁ , refl₂)

  symmetric : B.Symmetric R₁ → I.Symmetric B R₂ →
              B.Symmetric (Rel B R₁ R₂)
  symmetric sym₁ sym₂ (x₁Rx₂ , y₁Ry₂) = (sym₁ x₁Rx₂ , sym₂ y₁Ry₂)

  transitive : B.Transitive R₁ → I.Transitive B R₂ →
               B.Transitive (Rel B R₁ R₂)
  transitive trans₁ trans₂ (x₁Rx₂ , y₁Ry₂) (x₂Rx₃ , y₂Ry₃) =
    (trans₁ x₁Rx₂ x₂Rx₃ , trans₂ y₁Ry₂ y₂Ry₃)

  isEquivalence : B.IsEquivalence R₁ → I.IsEquivalence B R₂ →
                  B.IsEquivalence (Rel B R₁ R₂)
  isEquivalence eq₁ eq₂ = record
    { refl  = refl (B.IsEquivalence.refl eq₁)
                   (I.IsEquivalence.refl eq₂)
    ; sym   = symmetric (B.IsEquivalence.sym eq₁)
                        (I.IsEquivalence.sym eq₂)
    ; trans = transitive (B.IsEquivalence.trans eq₁)
                         (I.IsEquivalence.trans eq₂)
    }

open Dummy public

setoid : ∀ {b₁ b₂ i₁ i₂} →
         (A : B.Setoid b₁ b₂) → I.Setoid (B.Setoid.Carrier A) i₁ i₂ →
         B.Setoid _ _
setoid s₁ s₂ = record
  { isEquivalence = isEquivalence (B.Setoid.isEquivalence s₁)
                                  (I.Setoid.isEquivalence s₂)
  }

------------------------------------------------------------------------
-- The propositional equality setoid over sigma types can be
-- decomposed using Rel

Rel⇿≡ : ∀ {a b} {A : Set a} {B : A → Set b} →
        Inverse (setoid (P.setoid A) (H.indexedSetoid B))
                (P.setoid (Σ A B))
Rel⇿≡ {A = A} {B} = record
  { to         = record { _⟨$⟩_ = id; cong = to-cong   }
  ; from       = record { _⟨$⟩_ = id; cong = from-cong }
  ; inverse-of = record
    { left-inverse-of  = uncurry (λ _ _ → (P.refl , H.refl))
    ; right-inverse-of = λ _ → P.refl
    }
  }
  where
  open I using (_=[_]⇒_)

  to-cong : Rel B P._≡_ (λ x y → H._≅_ x y) =[ id ]⇒ P._≡_
  to-cong (P.refl , H.refl) = P.refl

  from-cong : P._≡_ =[ id ]⇒ Rel B P._≡_ (λ x y → H._≅_ x y)
  from-cong {i = (x , y)} P.refl = (P.refl , H.refl)

------------------------------------------------------------------------
-- Equivalences and inverses are also preserved

equivalent :
  ∀ {i} {I : Set i}
    {f₁ f₂ t₁ t₂} {From : I.Setoid I f₁ f₂} {To : I.Setoid I t₁ t₂} →
  (∀ {i} → Equivalent (From at i) (To at i)) →
  Equivalent (setoid (P.setoid I) From) (setoid (P.setoid I) To)
equivalent {I = I} {From = F} {T} F⇔T = record
  { to   = record { _⟨$⟩_ = to;   cong = to-cong   }
  ; from = record { _⟨$⟩_ = from; cong = from-cong }
  }
  where
  open B.Setoid (setoid (P.setoid I) F) using () renaming (_≈_ to _≈F_)
  open B.Setoid (setoid (P.setoid I) T) using () renaming (_≈_ to _≈T_)
  open B using (_=[_]⇒_)

  to = Prod.map id (F._⟨$⟩_ (Equivalent.to F⇔T))

  to-cong : _≈F_ =[ to ]⇒ _≈T_
  to-cong (P.refl , ∼) = (P.refl , F.cong (Equivalent.to F⇔T) ∼)

  from = Prod.map id (F._⟨$⟩_ (Equivalent.from F⇔T))

  from-cong : _≈T_ =[ from ]⇒ _≈F_
  from-cong (P.refl , ∼) = (P.refl , F.cong (Equivalent.from F⇔T) ∼)

⇔ : ∀ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
    (∀ {x} → B₁ x ⇔ B₂ x) → Σ A B₁ ⇔ Σ A B₂
⇔ {B₁ = B₁} {B₂} B₁⇔B₂ =
  Inverse.equivalent (Rel⇿≡ {B = B₂}) ⟨∘⟩
  equivalent (λ {x} →
    Inverse.equivalent (H.≡⇿≅ B₂) ⟨∘⟩
    B₁⇔B₂ {x} ⟨∘⟩
    Inverse.equivalent (Inv.sym (H.≡⇿≅ B₁))) ⟨∘⟩
  Eq.sym (Inverse.equivalent (Rel⇿≡ {B = B₁}))

inverse :
  ∀ {i} {I : Set i}
    {f₁ f₂ t₁ t₂} {From : I.Setoid I f₁ f₂} {To : I.Setoid I t₁ t₂} →
  (∀ {i} → Inverse (From at i) (To at i)) →
  Inverse (setoid (P.setoid I) From) (setoid (P.setoid I) To)
inverse {I = I} {From = F} {T} F⇿T = record
  { to         = Equivalent.to   eq
  ; from       = Equivalent.from eq
  ; inverse-of = record
    { left-inverse-of  = left
    ; right-inverse-of = right
    }
  }
  where
  eq = equivalent (Inverse.equivalent F⇿T)

  left : Equivalent.from eq LeftInverseOf Equivalent.to eq
  left (x , y) = (P.refl , Inverse.left-inverse-of F⇿T y)

  right : Equivalent.from eq RightInverseOf Equivalent.to eq
  right (x , y) = (P.refl , Inverse.right-inverse-of F⇿T y)

⇿ : ∀ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A → Set b₂} →
    (∀ {x} → B₁ x ⇿ B₂ x) → Σ A B₁ ⇿ Σ A B₂
⇿ {B₁ = B₁} {B₂} B₁⇿B₂ =
  Rel⇿≡ {B = B₂} ⟪∘⟫
  inverse (λ {x} → H.≡⇿≅ B₂ ⟪∘⟫ B₁⇿B₂ {x} ⟪∘⟫ Inv.sym (H.≡⇿≅ B₁)) ⟪∘⟫
  Inv.sym (Rel⇿≡ {B = B₁})
