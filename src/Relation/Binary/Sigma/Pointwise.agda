------------------------------------------------------------------------
-- Pointwise lifting of binary relations to sigma types
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Relation.Binary.Sigma.Pointwise where

open import Data.Product as Prod
open import Level
open import Function
open import Function.Equality as F using (_⟶_; _⟨$⟩_)
  renaming (_∘_ to _⊚_)
open import Function.Equivalence as Eq
  using (Equivalent; _⇔_; module Equivalent)
  renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse as Inv
  using (Inverse; _⇿_; module Inverse; Isomorphism)
  renaming (_∘_ to _⟪∘⟫_)
open import Function.LeftInverse
  using (_LeftInverseOf_; _RightInverseOf_)
open import Function.Surjection using (_↠_; module Surjection)
import Relation.Binary as B
open import Relation.Binary.Indexed as I using (_at_)
import Relation.Binary.HeterogeneousEquality as H
import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------
-- Pointwise lifting

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
Rel⇿≡ {a} {b} {A} {B} = record
  { to         = record { _⟨$⟩_ = id; cong = to-cong   }
  ; from       = record { _⟨$⟩_ = id; cong = from-cong }
  ; inverse-of = record
    { left-inverse-of  = uncurry (λ _ _ → (P.refl , H.refl))
    ; right-inverse-of = λ _ → P.refl
    }
  }
  where
  open I using (_=[_]⇒_)

  to-cong : Rel B P._≡_ (λ x y → H._≅_ x y) =[ id {a = a ⊔ b} ]⇒ P._≡_
  to-cong (P.refl , H.refl) = P.refl

  from-cong : P._≡_ =[ id {a = a ⊔ b} ]⇒ Rel B P._≡_ (λ x y → H._≅_ x y)
  from-cong {i = (x , y)} P.refl = (P.refl , H.refl)

------------------------------------------------------------------------
-- Equivalences and inverses are also preserved

equivalent :
  ∀ {a₁ a₂ b₁ b₁′ b₂ b₂′}
    {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : I.Setoid A₁ b₁ b₁′} {B₂ : I.Setoid A₂ b₂ b₂′}
  (A₁⇔A₂ : A₁ ⇔ A₂) →
  (∀ {x} → B₁ at x ⟶ B₂ at (Equivalent.to   A₁⇔A₂ ⟨$⟩ x)) →
  (∀ {y} → B₂ at y ⟶ B₁ at (Equivalent.from A₁⇔A₂ ⟨$⟩ y)) →
  Equivalent (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
equivalent {A₁ = A₁} {A₂} {B₁} {B₂} A₁⇔A₂ B-to B-from = record
  { to   = record { _⟨$⟩_ = to;   cong = to-cong   }
  ; from = record { _⟨$⟩_ = from; cong = from-cong }
  }
  where
  open B.Setoid (setoid (P.setoid A₁) B₁)
    using () renaming (_≈_ to _≈₁_)
  open B.Setoid (setoid (P.setoid A₂) B₂)
    using () renaming (_≈_ to _≈₂_)
  open B using (_=[_]⇒_)

  to = Prod.map (_⟨$⟩_ (Equivalent.to A₁⇔A₂)) (_⟨$⟩_ B-to)

  to-cong : _≈₁_ =[ to ]⇒ _≈₂_
  to-cong (P.refl , ∼) = (P.refl , F.cong B-to ∼)

  from = Prod.map (_⟨$⟩_ (Equivalent.from A₁⇔A₂)) (_⟨$⟩_ B-from)

  from-cong : _≈₂_ =[ from ]⇒ _≈₁_
  from-cong (P.refl , ∼) = (P.refl , F.cong B-from ∼)

equivalent′ :
  ∀ {a₁ a₂ b₁ b₁′ b₂ b₂′}
    {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : I.Setoid A₁ b₁ b₁′} (B₂ : I.Setoid A₂ b₂ b₂′)
  (A₁↠A₂ : A₁ ↠ A₂) →
  (∀ {x} → Equivalent (B₁ at x) (B₂ at (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
  Equivalent (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
equivalent′ {B₁ = B₁} B₂ A₁↠A₂ B₁⇔B₂ =
  equivalent (Surjection.equivalent A₁↠A₂) B-to B-from
  where
  B-to : ∀ {x} → B₁ at x ⟶ B₂ at (Surjection.to A₁↠A₂ ⟨$⟩ x)
  B-to = Equivalent.to B₁⇔B₂

  subst-cong : ∀ {i a p} {I : Set i} {A : I → Set a}
               (P : ∀ {i} → A i → A i → Set p) {i i′} {x y : A i}
               (i≡i′ : P._≡_ i i′) →
               P x y → P (P.subst A i≡i′ x) (P.subst A i≡i′ y)
  subst-cong P P.refl p = p

  B-from : ∀ {y} → B₂ at y ⟶ B₁ at (Surjection.from A₁↠A₂ ⟨$⟩ y)
  B-from = record
    { _⟨$⟩_ = λ x → Equivalent.from B₁⇔B₂ ⟨$⟩
                      P.subst (I.Setoid.Carrier B₂)
                         (P.sym $ Surjection.right-inverse-of A₁↠A₂ _)
                         x
    ; cong  = F.cong (Equivalent.from B₁⇔B₂) ∘
              subst-cong (λ {x} → I.Setoid._≈_ B₂ {x} {x})
                         (P.sym (Surjection.right-inverse-of A₁↠A₂ _))
    }

⇔ : ∀ {a₁ a₂ b₁ b₂}
      {A₁ : Set a₁} {A₂ : Set a₂}
      {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
    (A₁⇔A₂ : A₁ ⇔ A₂) →
    (∀ {x} → B₁ x → B₂ (Equivalent.to   A₁⇔A₂ ⟨$⟩ x)) →
    (∀ {y} → B₂ y → B₁ (Equivalent.from A₁⇔A₂ ⟨$⟩ y)) →
    Σ A₁ B₁ ⇔ Σ A₂ B₂
⇔ {B₁ = B₁} {B₂} A₁⇔A₂ B-to B-from =
  Inverse.equivalent (Rel⇿≡ {B = B₂}) ⟨∘⟩
  equivalent A₁⇔A₂
    (Inverse.to (H.≡⇿≅ B₂) ⊚ P.→-to-⟶ B-to ⊚ Inverse.from (H.≡⇿≅ B₁))
    (Inverse.to (H.≡⇿≅ B₁) ⊚ P.→-to-⟶ B-from ⊚ Inverse.from (H.≡⇿≅ B₂))
    ⟨∘⟩
  Eq.sym (Inverse.equivalent (Rel⇿≡ {B = B₁}))

⇔′ : ∀ {a₁ a₂ b₁ b₂}
       {A₁ : Set a₁} {A₂ : Set a₂}
       {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
     (A₁↠A₂ : A₁ ↠ A₂) →
     (∀ {x} → _⇔_ (B₁ x) (B₂ (Surjection.to A₁↠A₂ ⟨$⟩ x))) →
     _⇔_ (Σ A₁ B₁) (Σ A₂ B₂)
⇔′ {B₁ = B₁} {B₂} A₁↠A₂ B₁⇔B₂ =
  Inverse.equivalent (Rel⇿≡ {B = B₂}) ⟨∘⟩
  equivalent′ (H.indexedSetoid B₂) A₁↠A₂
    (λ {x} → Inverse.equivalent (H.≡⇿≅ B₂) ⟨∘⟩
             B₁⇔B₂ {x} ⟨∘⟩
             Inverse.equivalent (Inv.sym (H.≡⇿≅ B₁))) ⟨∘⟩
  Eq.sym (Inverse.equivalent (Rel⇿≡ {B = B₁}))

inverse :
  ∀ {a₁ a₂ b₁ b₁′ b₂ b₂′}
    {A₁ : Set a₁} {A₂ : Set a₂}
    {B₁ : I.Setoid A₁ b₁ b₁′} (B₂ : I.Setoid A₂ b₂ b₂′) →
  (A₁⇿A₂ : A₁ ⇿ A₂) →
  (∀ {x} → Inverse (B₁ at x) (B₂ at (Inverse.to A₁⇿A₂ ⟨$⟩ x))) →
  Inverse (setoid (P.setoid A₁) B₁) (setoid (P.setoid A₂) B₂)
inverse {A₁ = A₁} {A₂} {B₁} B₂ A₁⇿A₂ B₁⇿B₂ = record
  { to         = Equivalent.to   eq
  ; from       = Equivalent.from eq
  ; inverse-of = record
    { left-inverse-of  = left
    ; right-inverse-of = right
    }
  }
  where
  eq = equivalent′ B₂ (Inverse.surjection A₁⇿A₂)
                      (Inverse.equivalent B₁⇿B₂)

  left : Equivalent.from eq LeftInverseOf Equivalent.to eq
  left (x , y) =
    Inverse.left-inverse-of A₁⇿A₂ x ,
    I.Setoid.trans B₁
      (lemma (P.sym (Inverse.left-inverse-of A₁⇿A₂ x))
             (P.sym (Inverse.right-inverse-of A₁⇿A₂
                       (Inverse.to A₁⇿A₂ ⟨$⟩ x))))
      (Inverse.left-inverse-of B₁⇿B₂ y)
    where
    lemma :
      ∀ {x x′ y} → P._≡_ x x′ →
      (eq : P._≡_ (Inverse.to A₁⇿A₂ ⟨$⟩ x) (Inverse.to A₁⇿A₂ ⟨$⟩ x′)) →
      I.Setoid._≈_ B₁
        (Inverse.from B₁⇿B₂ ⟨$⟩ P.subst (I.Setoid.Carrier B₂) eq y)
        (Inverse.from B₁⇿B₂ ⟨$⟩ y)
    lemma P.refl P.refl = I.Setoid.refl B₁

  right : Equivalent.from eq RightInverseOf Equivalent.to eq
  right (x , y) =
    Inverse.right-inverse-of A₁⇿A₂ x ,
    I.Setoid.trans B₂
      (Inverse.right-inverse-of B₁⇿B₂
         (P.subst (I.Setoid.Carrier B₂) p y))
      (lemma p)
    where
    p = P.sym $ Inverse.right-inverse-of A₁⇿A₂ x

    lemma : ∀ {x x′ y} (eq : P._≡_ x x′) →
            I.Setoid._≈_ B₂
              (P.subst (I.Setoid.Carrier B₂) eq y)
              y
    lemma P.refl = I.Setoid.refl B₂

⇿ : ∀ {a₁ a₂ b₁ b₂}
      {A₁ : Set a₁} {A₂ : Set a₂}
      {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
    (A₁⇿A₂ : A₁ ⇿ A₂) →
    (∀ {x} → B₁ x ⇿ B₂ (Inverse.to A₁⇿A₂ ⟨$⟩ x)) →
    Σ A₁ B₁ ⇿ Σ A₂ B₂
⇿ {B₁ = B₁} {B₂} A₁⇿A₂ B₁⇿B₂ =
  Rel⇿≡ {B = B₂} ⟪∘⟫
  inverse (H.indexedSetoid B₂) A₁⇿A₂
    (λ {x} → H.≡⇿≅ B₂ ⟪∘⟫ B₁⇿B₂ {x} ⟪∘⟫ Inv.sym (H.≡⇿≅ B₁)) ⟪∘⟫
  Inv.sym (Rel⇿≡ {B = B₁})

cong : ∀ {k a₁ a₂ b₁ b₂}
         {A₁ : Set a₁} {A₂ : Set a₂}
         {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
       (A₁⇿A₂ : _⇿_ A₁ A₂) →
       (∀ {x} → Isomorphism k (B₁ x) (B₂ (Inverse.to A₁⇿A₂ ⟨$⟩ x))) →
       Isomorphism k (Σ A₁ B₁) (Σ A₂ B₂)
cong {k = Inv.equivalent} = ⇔′ ∘ Inverse.surjection
cong {k = Inv.inverse}    = ⇿
