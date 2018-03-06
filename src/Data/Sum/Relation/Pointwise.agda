------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise sum
------------------------------------------------------------------------

module Data.Sum.Relation.Pointwise where

open import Data.Sum as Sum
import Data.Sum.Relation.Core as Core
open import Data.Empty using (⊥)
open import Function
open import Function.Equality as F
  using (_⟶_; _⟨$⟩_)
open import Function.Equivalence as Eq
  using (Equivalence; _⇔_; module Equivalence)
open import Function.Injection as Inj
  using (Injection; _↣_; module Injection)
open import Function.Inverse as Inv
  using (Inverse; _↔_; module Inverse)
open import Function.LeftInverse as LeftInv
  using (LeftInverse; _↞_; module LeftInverse)
open import Function.Related
open import Function.Surjection as Surj
  using (Surjection; _↠_; module Surjection)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)

module _ {a₁ a₂} {A₁ : Set a₁} {A₂ : Set a₂} where

  ----------------------------------------------------------------------
  -- Pointwise sum

  open Core public using (₁∼₂; ₁∼₁; ₂∼₂)

  Pointwise : ∀ {ℓ₁ ℓ₂} → Rel A₁ ℓ₁ → Rel A₂ ℓ₂ → Rel (A₁ ⊎ A₂) _
  Pointwise = Core.⊎ʳ ⊥

  ----------------------------------------------------------------------
  -- Helpers

  ₁≁₂ : ∀ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} →
        ∀ {x y} → ¬ (Pointwise ∼₁ ∼₂ (inj₁ x) (inj₂ y))
  ₁≁₂ (₁∼₂ ())

  ----------------------------------------------------------------------
  -- Some properties which are preserved by Pointwise

  module _ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {∼₂ : Rel A₂ ℓ₂} where

    ⊎-refl : Reflexive ∼₁ → Reflexive ∼₂ →
             Reflexive (Pointwise ∼₁ ∼₂)
    ⊎-refl refl₁ refl₂ = Core._⊎-refl_ refl₁ refl₂

    ⊎-symmetric : Symmetric ∼₁ → Symmetric ∼₂ →
                  Symmetric (Pointwise ∼₁ ∼₂)
    ⊎-symmetric sym₁ sym₂ = sym
      where
      sym : Symmetric (Pointwise _ _)
      sym (₁∼₁ x₁∼y₁) = ₁∼₁ (sym₁ x₁∼y₁)
      sym (₂∼₂ x₂∼y₂) = ₂∼₂ (sym₂ x₂∼y₂)
      sym (₁∼₂ ())

    ⊎-transitive : Transitive ∼₁ → Transitive ∼₂ →
                   Transitive (Pointwise ∼₁ ∼₂)
    ⊎-transitive trans₁ trans₂ = Core._⊎-transitive_ trans₁ trans₂

    ⊎-asymmetric : Asymmetric ∼₁ → Asymmetric ∼₂ →
                   Asymmetric (Pointwise ∼₁ ∼₂)
    ⊎-asymmetric asym₁ asym₂ = Core._⊎-asymmetric_ asym₁ asym₂

    ⊎-substitutive : ∀ {ℓ₃} → Substitutive ∼₁ ℓ₃ → Substitutive ∼₂ ℓ₃ →
                     Substitutive (Pointwise ∼₁ ∼₂) ℓ₃
    ⊎-substitutive subst₁ subst₂ = subst
      where
      subst : Substitutive (Pointwise _ _) _
      subst P (₁∼₁ x∼y) Px = subst₁ (λ z → P (inj₁ z)) x∼y Px
      subst P (₂∼₂ x∼y) Px = subst₂ (λ z → P (inj₂ z)) x∼y Px
      subst P (₁∼₂ ())  Px

    ⊎-decidable : Decidable ∼₁ → Decidable ∼₂ →
                  Decidable (Pointwise ∼₁ ∼₂)
    ⊎-decidable dec₁ dec₂ = Core.⊎-decidable dec₁ dec₂ (no ₁≁₂)

  module _ {ℓ₁ ℓ₂} {∼₁ : Rel A₁ ℓ₁} {≈₁ : Rel A₁ ℓ₂}
           {ℓ₃ ℓ₄} {∼₂ : Rel A₂ ℓ₃} {≈₂ : Rel A₂ ℓ₄} where

    ⊎-reflexive : ≈₁ ⇒ ∼₁ → ≈₂ ⇒ ∼₂ →
                  (Pointwise ≈₁ ≈₂) ⇒ (Pointwise ∼₁ ∼₂)
    ⊎-reflexive refl₁ refl₂ = Core._⊎-reflexive_ refl₁ refl₂

    ⊎-irreflexive : Irreflexive ≈₁ ∼₁ → Irreflexive ≈₂ ∼₂ →
                    Irreflexive (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
    ⊎-irreflexive irrefl₁ irrefl₂ =
      Core._⊎-irreflexive_ irrefl₁ irrefl₂

    ⊎-antisymmetric : Antisymmetric ≈₁ ∼₁ → Antisymmetric ≈₂ ∼₂ →
                      Antisymmetric (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
    ⊎-antisymmetric antisym₁ antisym₂ =
      Core._⊎-antisymmetric_ antisym₁ antisym₂

    ⊎-respects₂ : ∼₁ Respects₂ ≈₁ → ∼₂ Respects₂ ≈₂ →
                  (Pointwise ∼₁ ∼₂) Respects₂ (Pointwise ≈₁ ≈₂)
    ⊎-respects₂ resp₁ resp₂ = Core._⊎-≈-respects₂_ resp₁ resp₂

  ----------------------------------------------------------------------
  -- Some collections of properties which are preserved

  module _ {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {≈₂ : Rel A₂ ℓ₂} where

    ⊎-isEquivalence : IsEquivalence ≈₁ → IsEquivalence ≈₂ →
                      IsEquivalence (Pointwise ≈₁ ≈₂)
    ⊎-isEquivalence eq₁ eq₂ = record
      { refl  = ⊎-refl       (refl  eq₁) (refl  eq₂)
      ; sym   = ⊎-symmetric  (sym   eq₁) (sym   eq₂)
      ; trans = ⊎-transitive (trans eq₁) (trans eq₂)
      }
      where open IsEquivalence

    ⊎-isDecEquivalence : IsDecEquivalence ≈₁ → IsDecEquivalence ≈₂ →
                         IsDecEquivalence (Pointwise ≈₁ ≈₂)
    ⊎-isDecEquivalence eq₁ eq₂ = record
      { isEquivalence =
          ⊎-isEquivalence (isEquivalence eq₁) (isEquivalence eq₂)
      ; _≟_           = ⊎-decidable (_≟_ eq₁) (_≟_ eq₂)
      }
      where open IsDecEquivalence

  module _ {ℓ₁ ℓ₂} {≈₁ : Rel A₁ ℓ₁} {∼₁ : Rel A₁ ℓ₂}
           {ℓ₃ ℓ₄} {≈₂ : Rel A₂ ℓ₃} {∼₂ : Rel A₂ ℓ₄} where

    ⊎-isPreorder : IsPreorder ≈₁ ∼₁ → IsPreorder ≈₂ ∼₂ →
                   IsPreorder (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
    ⊎-isPreorder pre₁ pre₂ = record
      { isEquivalence =
          ⊎-isEquivalence (isEquivalence pre₁) (isEquivalence pre₂)
      ; reflexive     = ⊎-reflexive (reflexive pre₁) (reflexive pre₂)
      ; trans         = ⊎-transitive (trans pre₁) (trans pre₂)
      }
      where open IsPreorder

    ⊎-isPartialOrder : IsPartialOrder ≈₁ ∼₁ →
                       IsPartialOrder ≈₂ ∼₂ →
                       IsPartialOrder
                         (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
    ⊎-isPartialOrder po₁ po₂ = record
      { isPreorder = ⊎-isPreorder (isPreorder po₁) (isPreorder po₂)
      ; antisym    = ⊎-antisymmetric (antisym po₁) (antisym    po₂)
      }
      where open IsPartialOrder

    ⊎-isStrictPartialOrder : IsStrictPartialOrder ≈₁ ∼₁ →
                             IsStrictPartialOrder ≈₂ ∼₂ →
                             IsStrictPartialOrder
                               (Pointwise ≈₁ ≈₂) (Pointwise ∼₁ ∼₂)
    ⊎-isStrictPartialOrder spo₁ spo₂ = record
      { isEquivalence =
          ⊎-isEquivalence (isEquivalence spo₁) (isEquivalence spo₂)
      ; irrefl        = ⊎-irreflexive   (irrefl spo₁) (irrefl   spo₂)
      ; trans         = ⊎-transitive    (trans spo₁)  (trans    spo₂)
      ; <-resp-≈      = ⊎-respects₂   (<-resp-≈ spo₁) (<-resp-≈ spo₂)
      }
      where open IsStrictPartialOrder

------------------------------------------------------------------------
-- "Packages" can also be combined.

module _ {a b c d} where

  ⊎-setoid : Setoid a b → Setoid c d → Setoid _ _
  ⊎-setoid s₁ s₂ = record
    { isEquivalence =
        ⊎-isEquivalence (isEquivalence s₁) (isEquivalence s₂)
    } where open Setoid

  ⊎-decSetoid : DecSetoid a b → DecSetoid c d → DecSetoid _ _
  ⊎-decSetoid ds₁ ds₂ = record
    { isDecEquivalence =
        ⊎-isDecEquivalence (isDecEquivalence ds₁) (isDecEquivalence ds₂)
    } where open DecSetoid

  -- Some additional notation for combining setoids
  infix 4 _⊎ₛ_
  _⊎ₛ_ : Setoid a b → Setoid c d → Setoid _ _
  _⊎ₛ_ = ⊎-setoid

module _ {a b c d e f} where

  ⊎-preorder : Preorder a b c → Preorder d e f → Preorder _ _ _
  ⊎-preorder p₁ p₂ = record
    { isPreorder   =
        ⊎-isPreorder (isPreorder p₁) (isPreorder p₂)
    } where open Preorder

  ⊎-poset : Poset a b c → Poset a b c → Poset _ _ _
  ⊎-poset po₁ po₂ = record
    { isPartialOrder =
        ⊎-isPartialOrder (isPartialOrder po₁) (isPartialOrder po₂)
    } where open Poset

------------------------------------------------------------------------
-- The propositional equality setoid over products can be
-- decomposed using ×-Rel

Pointwise-≡⇒≡ : ∀ {a b} {A : Set a} {B : Set b} →
         (Pointwise _≡_ _≡_) ⇒ _≡_ {A = A ⊎ B}
Pointwise-≡⇒≡ (₁∼₂ ())
Pointwise-≡⇒≡ (₁∼₁ P.refl) = P.refl
Pointwise-≡⇒≡ (₂∼₂ P.refl) = P.refl

≡⇒Pointwise-≡ : ∀ {a b} {A : Set a} {B : Set b} →
         _≡_ {A = A ⊎ B} ⇒ (Pointwise _≡_ _≡_)
≡⇒Pointwise-≡ P.refl = ⊎-refl P.refl P.refl

Pointwise-≡↔≡ : ∀ {a b} (A : Set a) (B : Set b) →
                Inverse ((P.setoid A) ⊎ₛ (P.setoid B))
                        (P.setoid (A ⊎ B))
Pointwise-≡↔≡ _ _ = record
  { to         = record { _⟨$⟩_ = id; cong = Pointwise-≡⇒≡ }
  ; from       = record { _⟨$⟩_ = id; cong = ≡⇒Pointwise-≡ }
  ; inverse-of = record
    { left-inverse-of  = λ _ → ⊎-refl P.refl P.refl
    ; right-inverse-of = λ _ → P.refl
    }
  }

_⊎-≟_ : ∀ {a b} {A : Set a} {B : Set b} →
        Decidable {A = A} _≡_ → Decidable {A = B} _≡_ →
        Decidable {A = A ⊎ B} _≡_
(dec₁ ⊎-≟ dec₂) s₁ s₂ = Dec.map′ Pointwise-≡⇒≡ ≡⇒Pointwise-≡ (s₁ ≟ s₂)
  where
  open DecSetoid (⊎-decSetoid (P.decSetoid dec₁) (P.decSetoid dec₂))

------------------------------------------------------------------------
-- Setoid "relatedness"

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
         where

  _⊎-⟶_ : A ⟶ B → C ⟶ D → (A ⊎ₛ C) ⟶ (B ⊎ₛ D)
  _⊎-⟶_ f g = record
    { _⟨$⟩_ = fg
    ; cong  = fg-cong
    }
    where
    open Setoid (A ⊎ₛ C) using () renaming (_≈_ to _≈AC_)
    open Setoid (B ⊎ₛ D) using () renaming (_≈_ to _≈BD_)

    fg = Sum.map (_⟨$⟩_ f) (_⟨$⟩_ g)

    fg-cong : _≈AC_ =[ fg ]⇒ _≈BD_
    fg-cong (₁∼₂ ())
    fg-cong (₁∼₁ x∼₁y) = ₁∼₁ $ F.cong f x∼₁y
    fg-cong (₂∼₂ x∼₂y) = ₂∼₂ $ F.cong g x∼₂y

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
         where

  _⊎-equivalence_ : Equivalence A B → Equivalence C D →
                    Equivalence (A ⊎ₛ C) (B ⊎ₛ D)
  A⇔B ⊎-equivalence C⇔D = record
    { to   = to   A⇔B ⊎-⟶ to   C⇔D
    ; from = from A⇔B ⊎-⟶ from C⇔D
    } where open Equivalence

  _⊎-injection_ : Injection A B → Injection C D →
                  Injection (A ⊎ₛ C) (B ⊎ₛ D)
  _⊎-injection_ A↣B C↣D = record
    { to        = to A↣B ⊎-⟶ to C↣D
    ; injective = inj _ _
    }
    where
    open Injection
    open Setoid (A ⊎ₛ C) using () renaming (_≈_ to _≈AC_)
    open Setoid (B ⊎ₛ D) using () renaming (_≈_ to _≈BD_)

    inj : ∀ x y →
          (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ x ≈BD (to A↣B ⊎-⟶ to C↣D) ⟨$⟩ y →
          x ≈AC y
    inj (inj₁ x) (inj₁ y) (₁∼₁ x∼₁y) = ₁∼₁ (injective A↣B x∼₁y)
    inj (inj₂ x) (inj₂ y) (₂∼₂ x∼₂y) = ₂∼₂ (injective C↣D x∼₂y)
    inj (inj₁ x) (inj₂ y) (₁∼₂ ())
    inj (inj₂ x) (inj₁ y) ()

  _⊎-left-inverse_ : LeftInverse A B → LeftInverse C D →
                     LeftInverse (A ⊎ₛ C) (B ⊎ₛ D)
  A↞B ⊎-left-inverse C↞D = record
    { to              = Equivalence.to   eq
    ; from            = Equivalence.from eq
    ; left-inverse-of = [ ₁∼₁ ∘ left-inverse-of A↞B
                        , ₂∼₂ ∘ left-inverse-of C↞D
                        ]
    }
    where
    open LeftInverse
    eq = LeftInverse.equivalence A↞B ⊎-equivalence
         LeftInverse.equivalence C↞D

module _ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂}
         {A : Setoid a₁ a₂} {B : Setoid b₁ b₂}
         {C : Setoid c₁ c₂} {D : Setoid d₁ d₂}
         where

  _⊎-surjection_ : Surjection A B → Surjection C D →
                   Surjection (A ⊎ₛ C) (B ⊎ₛ D)
  A↠B ⊎-surjection C↠D = record
    { to         = LeftInverse.from inv
    ; surjective = record
      { from             = LeftInverse.to inv
      ; right-inverse-of = LeftInverse.left-inverse-of inv
      }
    }
    where
    open Surjection
    inv = right-inverse A↠B ⊎-left-inverse right-inverse C↠D

  _⊎-inverse_ : Inverse A B → Inverse C D →
                Inverse (A ⊎ₛ C) (B ⊎ₛ D)
  A↔B ⊎-inverse C↔D = record
    { to         = Surjection.to   surj
    ; from       = Surjection.from surj
    ; inverse-of = record
      { left-inverse-of  = LeftInverse.left-inverse-of inv
      ; right-inverse-of = Surjection.right-inverse-of surj
      }
    }
    where
    open Inverse
    surj = Inverse.surjection   A↔B ⊎-surjection
           Inverse.surjection   C↔D
    inv  = Inverse.left-inverse A↔B ⊎-left-inverse
           Inverse.left-inverse C↔D

------------------------------------------------------------------------
-- Propositional "relatedness"

module _ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} where

  _⊎-⇔_ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
  _⊎-⇔_ A⇔B C⇔D =
    Inverse.equivalence (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A⇔B ⊎-equivalence C⇔D) ⟨∘⟩
    Eq.sym (Inverse.equivalence (Pointwise-≡↔≡ A C))
    where open Eq using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↣_ : A ↣ B → C ↣ D → (A ⊎ C) ↣ (B ⊎ D)
  _⊎-↣_ A↣B C↣D =
    Inverse.injection (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A↣B ⊎-injection C↣D) ⟨∘⟩
    Inverse.injection (Inv.sym (Pointwise-≡↔≡ A C))
    where open Inj using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↞_ : A ↞ B → C ↞ D → (A ⊎ C) ↞ (B ⊎ D)
  _⊎-↞_ A↞B C↞D =
    Inverse.left-inverse (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A↞B ⊎-left-inverse C↞D) ⟨∘⟩
    Inverse.left-inverse (Inv.sym (Pointwise-≡↔≡ A C))
    where open LeftInv using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↠_ : A ↠ B → C ↠ D → (A ⊎ C) ↠ (B ⊎ D)
  _⊎-↠_ A↠B C↠D =
    Inverse.surjection (Pointwise-≡↔≡ B D) ⟨∘⟩
    (A↠B ⊎-surjection C↠D) ⟨∘⟩
    Inverse.surjection (Inv.sym (Pointwise-≡↔≡ A C))
    where open Surj using () renaming (_∘_ to _⟨∘⟩_)

  _⊎-↔_ : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
  _⊎-↔_ A↔B C↔D =
    Pointwise-≡↔≡ B D ⟨∘⟩
    (A↔B ⊎-inverse C↔D) ⟨∘⟩
    Inv.sym (Pointwise-≡↔≡ A C)
    where open Inv using () renaming (_∘_ to _⟨∘⟩_)

_⊎-cong_ : ∀ {k a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
           A ∼[ k ] B → C ∼[ k ] D → (A ⊎ C) ∼[ k ] (B ⊎ D)
_⊎-cong_ {implication}         = Sum.map
_⊎-cong_ {reverse-implication} = λ f g → lam (Sum.map (app-← f) (app-← g))
_⊎-cong_ {equivalence}         = _⊎-⇔_
_⊎-cong_ {injection}           = _⊎-↣_
_⊎-cong_ {reverse-injection}   = λ f g → lam (app-↢ f ⊎-↣ app-↢ g)
_⊎-cong_ {left-inverse}        = _⊎-↞_
_⊎-cong_ {surjection}          = _⊎-↠_
_⊎-cong_ {bijection}           = _⊎-↔_
