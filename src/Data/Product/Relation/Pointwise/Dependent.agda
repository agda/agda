------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of binary relations to sigma types
------------------------------------------------------------------------

module Data.Product.Relation.Pointwise.Dependent where

open import Data.Product as Prod
open import Level
open import Function
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection; Injective)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; module LeftInverse;
         _LeftInverseOf_; _RightInverseOf_)
open import Function.Related as Related
  using (_∼[_]_; lam; app-←; app-↢)
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
open import Relation.Binary as B using (_⇒_)
open import Relation.Binary.Indexed as I using (_at_)
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Pointwise lifting

infixr 4 _,_

record REL {a₁ a₂ b₁ b₂ ℓ₁ ℓ₂}
           {A₁ : Set a₁} (B₁ : A₁ → Set b₁)
           {A₂ : Set a₂} (B₂ : A₂ → Set b₂)
           (_R₁_ : B.REL A₁ A₂ ℓ₁) (_R₂_ : I.REL B₁ B₂ ℓ₂)
           (xy₁ : Σ A₁ B₁) (xy₂ : Σ A₂ B₂)
           : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    proj₁ : (proj₁ xy₁) R₁ (proj₁ xy₂)
    proj₂ : (proj₂ xy₁) R₂ (proj₂ xy₂)

open REL public

Pointwise : ∀ {a b ℓ₁ ℓ₂} {A : Set a} (B : A → Set b)
            (_R₁_ : B.Rel A ℓ₁) (_R₂_ : I.Rel B ℓ₂) → B.Rel (Σ A B) _
Pointwise B = REL B B

------------------------------------------------------------------------
-- Pointwise preserves many relational properties

module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b}
         {R₁ : B.Rel A ℓ₁} {R₂ : I.Rel B ℓ₂} where

  refl : B.Reflexive R₁ → I.Reflexive B R₂ →
         B.Reflexive (Pointwise B R₁ R₂)
  refl refl₁ refl₂ = (refl₁ , refl₂)

  symmetric : B.Symmetric R₁ → I.Symmetric B R₂ →
              B.Symmetric (Pointwise B R₁ R₂)
  symmetric sym₁ sym₂ (x₁Rx₂ , y₁Ry₂) = (sym₁ x₁Rx₂ , sym₂ y₁Ry₂)

  transitive : B.Transitive R₁ → I.Transitive B R₂ →
               B.Transitive (Pointwise B R₁ R₂)
  transitive trans₁ trans₂ (x₁Rx₂ , y₁Ry₂) (x₂Rx₃ , y₂Ry₃) =
    (trans₁ x₁Rx₂ x₂Rx₃ , trans₂ y₁Ry₂ y₂Ry₃)

  isEquivalence : B.IsEquivalence R₁ → I.IsEquivalence B R₂ →
                  B.IsEquivalence (Pointwise B R₁ R₂)
  isEquivalence eq₁ eq₂ = record
    { refl  = refl (B.IsEquivalence.refl eq₁)
                   (I.IsEquivalence.refl eq₂)
    ; sym   = symmetric (B.IsEquivalence.sym eq₁)
                        (I.IsEquivalence.sym eq₂)
    ; trans = transitive (B.IsEquivalence.trans eq₁)
                         (I.IsEquivalence.trans eq₂)
    }

setoid : ∀ {b₁ b₂ i₁ i₂} →
         (A : B.Setoid b₁ b₂) → I.Setoid (B.Setoid.Carrier A) i₁ i₂ →
         B.Setoid _ _
setoid s₁ s₂ = record
  { isEquivalence = isEquivalence (B.Setoid.isEquivalence s₁)
                                  (I.Setoid.isEquivalence s₂)
  }

------------------------------------------------------------------------
-- The propositional equality setoid over sigma types can be
-- decomposed using Pointwise

module _ {a b} {A : Set a} {B : A → Set b} where

  Pointwise-≡⇒≡ : Pointwise B _≡_ (λ x y → x H.≅ y) ⇒ _≡_
  Pointwise-≡⇒≡ (P.refl , H.refl) = P.refl

  ≡⇒Pointwise-≡ : _≡_ ⇒ Pointwise B _≡_ (λ x y → x H.≅ y)
  ≡⇒Pointwise-≡ P.refl = (P.refl , H.refl)

  Pointwise-≡↔≡ : Inverse (setoid (P.setoid A) (H.indexedSetoid B))
                  (P.setoid (Σ A B))
  Pointwise-≡↔≡ = record
    { to         = record { _⟨$⟩_ = id; cong = Pointwise-≡⇒≡ }
    ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Pointwise-≡ }
    ; inverse-of = record
      { left-inverse-of  = uncurry (λ _ _ → (P.refl , H.refl))
      ; right-inverse-of = λ _ → P.refl
      }
    }

------------------------------------------------------------------------
-- Properties related to "relatedness"
------------------------------------------------------------------------

private

  subst-cong : ∀ {i a p} {I : Set i} {A : I → Set a}
               (P : ∀ {i} → A i → A i → Set p) {i i′} {x y : A i}
               (i≡i′ : i P.≡ i′) →
               P x y → P (P.subst A i≡i′ x) (P.subst A i≡i′ y)
  subst-cong P P.refl p = p

⟶ : ∀ {a₁ a₂ b₁ b₁′ b₂ b₂′}
      {A₁ : Set a₁} {A₂ : Set a₂}
      {B₁ : I.Setoid A₁ b₁ b₁′} (B₂ : I.Setoid A₂ b₂ b₂′)
    (f : A₁ → A₂) → (∀ {x} → (B₁ at x) ⟶ (B₂ at f x)) →
    setoid (P.setoid A₁) B₁ ⟶ setoid (P.setoid A₂) B₂
⟶ {A₁ = A₁} {A₂} {B₁} B₂ f g = record
  { _⟨$⟩_ = fg
  ; cong  = fg-cong
  }
  where
  open B.Setoid (setoid (P.setoid A₁) B₁)
    using () renaming (_≈_ to _≈₁_)
  open B.Setoid (setoid (P.setoid A₂) B₂)
    using () renaming (_≈_ to _≈₂_)
  open B using (_=[_]⇒_)

  fg = Prod.map f (_⟨$⟩_ g)

  fg-cong : _≈₁_ =[ fg ]⇒ _≈₂_
  fg-cong (P.refl , ∼) = (P.refl , F.cong g ∼)


module _ {a₁ a₂ b₁ b₁′ b₂ b₂′} {A₁ : Set a₁} {A₂ : Set a₂} where

  equivalence : {B₁ : I.Setoid A₁ b₁ b₁′} {B₂ : I.Setoid A₂ b₂ b₂′}
    (A₁⇔A₂ : A₁ ⇔ A₂) →
    (∀ {x} → _⟶_ (B₁ at x) (B₂ at (Equivalence.to   A₁⇔A₂ ⟨$⟩ x))) →
    (∀ {y} → _⟶_ (B₂ at y) (B₁ at (Equivalence.from A₁⇔A₂ ⟨$⟩ y))) →
    Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  equivalence {B₁} {B₂} A₁⇔A₂ B-to B-from = record
    { to   = ⟶ B₂ (_⟨$⟩_ (to   A₁⇔A₂)) B-to
    ; from = ⟶ B₁ (_⟨$⟩_ (from A₁⇔A₂)) B-from
    } where open Equivalence

  equivalence-↞ : (B₁ : I.Setoid A₁ b₁ b₁′) {B₂ : I.Setoid A₂ b₂ b₂′}
    (A₁↞A₂ : A₁ ↞ A₂) →
    (∀ {x} → Equivalence (B₁ at (LeftInverse.from A₁↞A₂ ⟨$⟩ x))
                         (B₂ at x)) →
    Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  equivalence-↞ B₁ {B₂} A₁↞A₂ B₁⇔B₂ =
    equivalence (LeftInverse.equivalence A₁↞A₂) B-to B-from
    where
    B-to : ∀ {x} → _⟶_ (B₁ at x) (B₂ at (LeftInverse.to A₁↞A₂ ⟨$⟩ x))
    B-to = record
      { _⟨$⟩_ = λ x → Equivalence.to B₁⇔B₂ ⟨$⟩
                      P.subst (I.Setoid.Carrier B₁)
                         (P.sym $ LeftInverse.left-inverse-of A₁↞A₂ _)
                         x
      ; cong  = F.cong (Equivalence.to B₁⇔B₂) ∘
              subst-cong (λ {x} → I.Setoid._≈_ B₁ {x} {x})
                         (P.sym (LeftInverse.left-inverse-of A₁↞A₂ _))
      }

    B-from : ∀ {y} → _⟶_ (B₂ at y) (B₁ at (LeftInverse.from A₁↞A₂ ⟨$⟩ y))
    B-from = Equivalence.from B₁⇔B₂

  equivalence-↠ : {B₁ : I.Setoid A₁ b₁ b₁′} (B₂ : I.Setoid A₂ b₂ b₂′)
    (A₁↠A₂ : A₁ ↠ A₂) →
    (∀ {x} → Equivalence (B₁ at x) (B₂ at (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
    Equivalence (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  equivalence-↠ {B₁ = B₁} B₂ A₁↠A₂ B₁⇔B₂ =
    equivalence (Surjection.equivalence A₁↠A₂) B-to B-from
    where
    B-to : ∀ {x} → _⟶_ (B₁ at x) (B₂ at (Surjection.to A₁↠A₂ ⟨$⟩ x))
    B-to = Equivalence.to B₁⇔B₂

    B-from : ∀ {y} → _⟶_ (B₂ at y) (B₁ at (Surjection.from A₁↠A₂ ⟨$⟩ y))
    B-from = record
      { _⟨$⟩_ = λ x → Equivalence.from B₁⇔B₂ ⟨$⟩
                      P.subst (I.Setoid.Carrier B₂)
                         (P.sym $ Surjection.right-inverse-of A₁↠A₂ _)
                         x
      ; cong  = F.cong (Equivalence.from B₁⇔B₂) ∘
              subst-cong (λ {x} → I.Setoid._≈_ B₂ {x} {x})
                         (P.sym (Surjection.right-inverse-of A₁↠A₂ _))
      }

  injection : {B₁ : I.Setoid A₁ b₁ b₁′} (B₂ : I.Setoid A₂ b₂ b₂′) →
    (A₁↣A₂ : A₁ ↣ A₂) →
    (∀ {x} → Injection (B₁ at x) (B₂ at (Injection.to A₁↣A₂ ⟨$⟩ x))) →
    Injection (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  injection {B₁ = B₁} B₂ A₁↣A₂ B₁↣B₂ = record
    { to        = to
    ; injective = inj
    }
    where
    to = ⟶ B₂ (Injection.to A₁↣A₂ ⟨$⟩_) (Injection.to B₁↣B₂)

    inj : Injective to
    inj (x , y) =
      Injection.injective A₁↣A₂ x ,
      lemma (Injection.injective A₁↣A₂ x) y
      where
      lemma :
        ∀ {x x′}
          {y : I.Setoid.Carrier B₁ x} {y′ : I.Setoid.Carrier B₁ x′} →
        x ≡ x′ →
        (eq : I.Setoid._≈_ B₂ (Injection.to B₁↣B₂ ⟨$⟩ y)
                              (Injection.to B₁↣B₂ ⟨$⟩ y′)) →
        I.Setoid._≈_ B₁ y y′
      lemma P.refl = Injection.injective B₁↣B₂

  left-inverse : (B₁ : I.Setoid A₁ b₁ b₁′) {B₂ : I.Setoid A₂ b₂ b₂′} →
    (A₁↞A₂ : A₁ ↞ A₂) →
    (∀ {x} → LeftInverse (B₁ at (LeftInverse.from A₁↞A₂ ⟨$⟩ x))
                         (B₂ at x)) →
    LeftInverse (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  left-inverse B₁ {B₂} A₁↞A₂ B₁↞B₂ = record
    { to              = Equivalence.to   eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = left
    }
    where
    eq = equivalence-↞ B₁ A₁↞A₂ (LeftInverse.equivalence B₁↞B₂)

    left : Equivalence.from eq LeftInverseOf Equivalence.to eq
    left (x , y) =
      LeftInverse.left-inverse-of A₁↞A₂ x ,
      I.Setoid.trans B₁
        (LeftInverse.left-inverse-of B₁↞B₂ _)
        (lemma (P.sym (LeftInverse.left-inverse-of A₁↞A₂ x)))
      where
      lemma :
        ∀ {x x′ y} (eq : x ≡ x′) →
        I.Setoid._≈_ B₁ (P.subst (I.Setoid.Carrier B₁) eq y) y
      lemma P.refl = I.Setoid.refl B₁

  surjection : {B₁ : I.Setoid A₁ b₁ b₁′} (B₂ : I.Setoid A₂ b₂ b₂′) →
    (A₁↠A₂ : A₁ ↠ A₂) →
    (∀ {x} → Surjection (B₁ at x) (B₂ at (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
    Surjection (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  surjection B₂ A₁↠A₂ B₁↠B₂ = record
    { to         = Equivalence.to eq
    ; surjective = record
      { from             = Equivalence.from eq
      ; right-inverse-of = right
      }
    }
    where
    eq = equivalence-↠ B₂ A₁↠A₂ (Surjection.equivalence B₁↠B₂)

    right : Equivalence.from eq RightInverseOf Equivalence.to eq
    right (x , y) =
      Surjection.right-inverse-of A₁↠A₂ x ,
      I.Setoid.trans B₂
        (Surjection.right-inverse-of B₁↠B₂ _)
        (lemma (P.sym $ Surjection.right-inverse-of A₁↠A₂ x))
      where
      lemma : ∀ {x x′ y} (eq : x ≡ x′) →
              I.Setoid._≈_ B₂ (P.subst (I.Setoid.Carrier B₂) eq y) y
      lemma P.refl = I.Setoid.refl B₂

  inverse : {B₁ : I.Setoid A₁ b₁ b₁′} (B₂ : I.Setoid A₂ b₂ b₂′) →
    (A₁↔A₂ : A₁ ↔ A₂) →
    (∀ {x} → Inverse (B₁ at x) (B₂ at (Inverse.to A₁↔A₂ ⟨$⟩ x))) →
    Inverse (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
  inverse {B₁} B₂ A₁↔A₂ B₁↔B₂ = record
    { to         = Surjection.to   surj
    ; from       = Surjection.from surj
    ; inverse-of = record
      { left-inverse-of  = left
      ; right-inverse-of = Surjection.right-inverse-of surj
      }
    }
    where
    surj = surjection B₂ (Inverse.surjection A₁↔A₂)
                         (Inverse.surjection B₁↔B₂)

    left : Surjection.from surj LeftInverseOf Surjection.to surj
    left (x , y) =
      Inverse.left-inverse-of A₁↔A₂ x ,
      I.Setoid.trans B₁
        (lemma (P.sym (Inverse.left-inverse-of A₁↔A₂ x))
               (P.sym (Inverse.right-inverse-of A₁↔A₂
                       (Inverse.to A₁↔A₂ ⟨$⟩ x))))
        (Inverse.left-inverse-of B₁↔B₂ y)
      where
      lemma :
        ∀ {x x′ y} → x ≡ x′ →
        (eq : (Inverse.to A₁↔A₂ ⟨$⟩ x) ≡ (Inverse.to A₁↔A₂ ⟨$⟩ x′)) →
        I.Setoid._≈_ B₁
          (Inverse.from B₁↔B₂ ⟨$⟩ P.subst (I.Setoid.Carrier B₂) eq y)
          (Inverse.from B₁↔B₂ ⟨$⟩ y)
      lemma P.refl P.refl = I.Setoid.refl B₁

------------------------------------------------------------------------

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂}
         {b₁ b₂} {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
         where

  ⇔ : (A₁⇔A₂ : A₁ ⇔ A₂) →
      (∀ {x} → B₁ x → B₂ (Equivalence.to   A₁⇔A₂ ⟨$⟩ x)) →
      (∀ {y} → B₂ y → B₁ (Equivalence.from A₁⇔A₂ ⟨$⟩ y)) →
      Σ A₁ B₁ ⇔ Σ A₂ B₂
  ⇔ A₁⇔A₂ B-to B-from =
    Inverse.equivalence Pointwise-≡↔≡ ⟨∘⟩
    equivalence A₁⇔A₂
      (Inverse.to (H.≡↔≅ B₂) ⊚ P.→-to-⟶ B-to   ⊚ Inverse.from (H.≡↔≅ B₁))
      (Inverse.to (H.≡↔≅ B₁) ⊚ P.→-to-⟶ B-from ⊚ Inverse.from (H.≡↔≅ B₂))
      ⟨∘⟩
    Eq.sym (Inverse.equivalence (Pointwise-≡↔≡ {B = B₁}))
    where
    open Eq using () renaming (_∘_ to _⟨∘⟩_)
    open F  using () renaming (_∘_ to _⊚_)

  ⇔-↠ : ∀ (A₁↠A₂ : A₁ ↠ A₂) →
        (∀ {x} → _⇔_ (B₁ x) (B₂ (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
        _⇔_ (Σ A₁ B₁) (Σ A₂ B₂)
  ⇔-↠ A₁↠A₂ B₁⇔B₂ =
    Inverse.equivalence Pointwise-≡↔≡ ⟨∘⟩
    equivalence-↠ (H.indexedSetoid B₂) A₁↠A₂
      (Inverse.equivalence (H.≡↔≅ B₂) ⟨∘⟩
       B₁⇔B₂ ⟨∘⟩
       Inverse.equivalence (Inv.sym (H.≡↔≅ B₁))) ⟨∘⟩
    Eq.sym (Inverse.equivalence Pointwise-≡↔≡)
    where open Eq using () renaming (_∘_ to _⟨∘⟩_)

  ↣ : ∀ (A₁↣A₂ : A₁ ↣ A₂) →
      (∀ {x} → B₁ x ↣ B₂ (Injection.to A₁↣A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↣ Σ A₂ B₂
  ↣ A₁↣A₂ B₁↣B₂ =
    Inverse.injection Pointwise-≡↔≡ ⟨∘⟩
    injection (H.indexedSetoid B₂) A₁↣A₂
      (Inverse.injection (H.≡↔≅ B₂) ⟨∘⟩
       B₁↣B₂ ⟨∘⟩
       Inverse.injection (Inv.sym (H.≡↔≅ B₁))) ⟨∘⟩
    Inverse.injection (Inv.sym Pointwise-≡↔≡)
    where open Inj using () renaming (_∘_ to _⟨∘⟩_)

  ↞ : (A₁↞A₂ : A₁ ↞ A₂) →
      (∀ {x} → B₁ (LeftInverse.from A₁↞A₂ ⟨$⟩ x) ↞ B₂ x) →
      Σ A₁ B₁ ↞ Σ A₂ B₂
  ↞ A₁↞A₂ B₁↞B₂ =
    Inverse.left-inverse Pointwise-≡↔≡ ⟨∘⟩
    left-inverse (H.indexedSetoid B₁) A₁↞A₂
      (Inverse.left-inverse (H.≡↔≅ B₂) ⟨∘⟩
       B₁↞B₂ ⟨∘⟩
       Inverse.left-inverse (Inv.sym (H.≡↔≅ B₁))) ⟨∘⟩
    Inverse.left-inverse (Inv.sym Pointwise-≡↔≡)
    where open LeftInv using () renaming (_∘_ to _⟨∘⟩_)

  ↠ : (A₁↠A₂ : A₁ ↠ A₂) →
      (∀ {x} → B₁ x ↠ B₂ (Surjection.to A₁↠A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↠ Σ A₂ B₂
  ↠ A₁↠A₂ B₁↠B₂ =
    Inverse.surjection Pointwise-≡↔≡ ⟨∘⟩
    surjection (H.indexedSetoid B₂) A₁↠A₂
      (Inverse.surjection (H.≡↔≅ B₂) ⟨∘⟩
       B₁↠B₂ ⟨∘⟩
       Inverse.surjection (Inv.sym (H.≡↔≅ B₁))) ⟨∘⟩
    Inverse.surjection (Inv.sym Pointwise-≡↔≡)
    where open Surj using () renaming (_∘_ to _⟨∘⟩_)

  ↔ : (A₁↔A₂ : A₁ ↔ A₂) →
      (∀ {x} → B₁ x ↔ B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
      Σ A₁ B₁ ↔ Σ A₂ B₂
  ↔ A₁↔A₂ B₁↔B₂ =
    Pointwise-≡↔≡ ⟨∘⟩
    inverse (H.indexedSetoid B₂) A₁↔A₂
      (H.≡↔≅ B₂ ⟨∘⟩ B₁↔B₂ ⟨∘⟩ Inv.sym (H.≡↔≅ B₁)) ⟨∘⟩
    Inv.sym Pointwise-≡↔≡
    where open Inv using () renaming (_∘_ to _⟨∘⟩_)

private

  swap-coercions : ∀ {k a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : A₁ → Set b₁} (B₂ : A₂ → Set b₂)
    (A₁↔A₂ : _↔_ A₁ A₂) →
    (∀ {x} → B₁ x ∼[ k ] B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
    ∀ {x} → B₁ (Inverse.from A₁↔A₂ ⟨$⟩ x) ∼[ k ] B₂ x
  swap-coercions {k} {B₁ = B₁} B₂ A₁↔A₂ eq {x} =
    B₁ (Inverse.from A₁↔A₂ ⟨$⟩ x)
      ∼⟨ eq ⟩
    B₂ (Inverse.to A₁↔A₂ ⟨$⟩ (Inverse.from A₁↔A₂ ⟨$⟩ x))
      ↔⟨ B.Setoid.reflexive (Related.setoid Related.bijection _)
         (P.cong B₂ $ Inverse.right-inverse-of A₁↔A₂ x) ⟩
    B₂ x
      ∎
    where open Related.EquationalReasoning

cong : ∀ {k a₁ a₂ b₁ b₂}
         {A₁ : Set a₁} {A₂ : Set a₂}
         {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
       (A₁↔A₂ : _↔_ A₁ A₂) →
       (∀ {x} → B₁ x ∼[ k ] B₂ (Inverse.to A₁↔A₂ ⟨$⟩ x)) →
       Σ A₁ B₁ ∼[ k ] Σ A₂ B₂
cong {Related.implication}                   =
  λ A₁↔A₂ → Prod.map (_⟨$⟩_ (Inverse.to A₁↔A₂))
cong {Related.reverse-implication} {B₂ = B₂} =
  λ A₁↔A₂ B₁←B₂ → lam (Prod.map (_⟨$⟩_ (Inverse.from A₁↔A₂))
    (app-← (swap-coercions B₂ A₁↔A₂ B₁←B₂)))
cong {Related.equivalence}                   = ⇔-↠ ∘ Inverse.surjection
cong {Related.injection}                     = ↣ ∘ Inverse.injection
cong {Related.reverse-injection}   {B₂ = B₂} =
  λ A₁↔A₂ B₁↢B₂ → lam (↣ (Inverse.injection (Inv.sym A₁↔A₂))
    (app-↢ (swap-coercions B₂ A₁↔A₂ B₁↢B₂)))
cong {Related.left-inverse}                  =
  λ A₁↔A₂ → ↞ (Inverse.left-inverse A₁↔A₂) ∘ swap-coercions _ A₁↔A₂
cong {Related.surjection}                    = ↠ ∘ Inverse.surjection
cong {Related.bijection}                     = ↔

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

Rel    = Pointwise
Rel↔≡  = Pointwise-≡↔≡
