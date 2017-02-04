------------------------------------------------------------------------
-- The Agda standard library
--
-- Container combinators
------------------------------------------------------------------------

module Data.Container.Combinator where

open import Data.Container
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product as Prod hiding (Σ) renaming (_×_ to _⟨×⟩_)
open import Data.Sum renaming (_⊎_ to _⟨⊎⟩_)
open import Data.Unit.Base using (⊤)
open import Function as F hiding (id; const) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse using (_↔_)
open import Level
open import Relation.Binary.PropositionalEquality as P
  using (_≗_; refl)

------------------------------------------------------------------------
-- Combinators

-- Identity.

id : ∀ {c} → Container c
id = Lift ⊤ ▷ F.const (Lift ⊤)

-- Constant.

const : ∀ {c} → Set c → Container c
const X = X ▷ F.const (Lift ⊥)

-- Composition.

infixr 9 _∘_

_∘_ : ∀ {c} → Container c → Container c → Container c
C₁ ∘ C₂ = ⟦ C₁ ⟧ (Shape C₂) ▷ ◇ (Position C₂)

-- Product. (Note that, up to isomorphism, this is a special case of
-- indexed product.)

infixr 2 _×_

_×_ : ∀ {c} → Container c → Container c → Container c
C₁ × C₂ =
  (Shape C₁ ⟨×⟩ Shape C₂) ▷
  uncurry (λ s₁ s₂ → Position C₁ s₁ ⟨⊎⟩ Position C₂ s₂)

-- Indexed product.

Π : ∀ {c} {I : Set c} → (I → Container c) → Container c
Π C = (∀ i → Shape (C i)) ▷ λ s → ∃ λ i → Position (C i) (s i)

-- Sum. (Note that, up to isomorphism, this is a special case of
-- indexed sum.)

infixr 1 _⊎_

_⊎_ : ∀ {c} → Container c → Container c → Container c
C₁ ⊎ C₂ = (Shape C₁ ⟨⊎⟩ Shape C₂) ▷ [ Position C₁ , Position C₂ ]

-- Indexed sum.

Σ : ∀ {c} {I : Set c} → (I → Container c) → Container c
Σ C = (∃ λ i → Shape (C i)) ▷ λ s → Position (C (proj₁ s)) (proj₂ s)

-- Constant exponentiation. (Note that this is a special case of
-- indexed product.)

infix 0 const[_]⟶_

const[_]⟶_ : ∀ {c} → Set c → Container c → Container c
const[ X ]⟶ C = Π {I = X} (F.const C)

------------------------------------------------------------------------
-- Correctness proofs

-- I have proved some of the correctness statements under the
-- assumption of functional extensionality. I could have reformulated
-- the statements using suitable setoids, but I could not be bothered.

module Identity where

  correct : ∀ {c} {X : Set c} → ⟦ id {c} ⟧ X ↔ F.id X
  correct {c} = record
    { to         = P.→-to-⟶ {a  = c} λ xs → proj₂ xs _
    ; from       = P.→-to-⟶ {b₁ = c} λ x → (_ , λ _ → x)
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }

module Constant (ext : ∀ {ℓ} → P.Extensionality ℓ ℓ) where

  correct : ∀ {ℓ} (X : Set ℓ) {Y} → ⟦ const X ⟧ Y ↔ F.const X Y
  correct X {Y} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = λ _ → refl
      ; left-inverse-of  =
          λ xs → P.cong (_,_ (proj₁ xs)) (ext (λ x → ⊥-elim (lower x)))
      }
    }
    where
    to : ⟦ const X ⟧ Y → X
    to = proj₁

    from : X → ⟦ const X ⟧ Y
    from = < F.id , F.const (⊥-elim ∘′ lower) >

module Composition where

  correct : ∀ {c} (C₁ C₂ : Container c) {X : Set c} →
            ⟦ C₁ ∘ C₂ ⟧ X ↔ (⟦ C₁ ⟧ ⟨∘⟩ ⟦ C₂ ⟧) X
  correct C₁ C₂ {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ C₁ ∘ C₂ ⟧ X → ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)
    to ((s , f) , g) = (s , < f , curry g >)

    from : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) → ⟦ C₁ ∘ C₂ ⟧ X
    from (s , f) = ((s , proj₁ ⟨∘⟩ f) , uncurry (proj₂ ⟨∘⟩ f))

module Product (ext : ∀ {ℓ} → P.Extensionality ℓ ℓ) where

  correct : ∀ {c} (C₁ C₂ : Container c) {X : Set c} →
            ⟦ C₁ × C₂ ⟧ X ↔ (⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X)
  correct {c} C₁ C₂ {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ C₁ × C₂ ⟧ X → ⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X
    to ((s₁ , s₂) , f) = ((s₁ , f ⟨∘⟩ inj₁) , (s₂ , f ⟨∘⟩ inj₂))

    from : ⟦ C₁ ⟧ X ⟨×⟩ ⟦ C₂ ⟧ X → ⟦ C₁ × C₂ ⟧ X
    from ((s₁ , f₁) , (s₂ , f₂)) = ((s₁ , s₂) , [ f₁ , f₂ ])

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (s , f) =
      P.cong (_,_ s) (ext {ℓ = c} [ (λ _ → refl) , (λ _ → refl) ])

module IndexedProduct where

  correct : ∀ {c I} (C : I → Container c) {X : Set c} →
            ⟦ Π C ⟧ X ↔ (∀ i → ⟦ C i ⟧ X)
  correct {I = I} C {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ Π C ⟧ X → ∀ i → ⟦ C i ⟧ X
    to (s , f) = λ i → (s i , λ p → f (i , p))

    from : (∀ i → ⟦ C i ⟧ X) → ⟦ Π C ⟧ X
    from f = (proj₁ ⟨∘⟩ f , uncurry (proj₂ ⟨∘⟩ f))

module Sum where

  correct : ∀ {c} (C₁ C₂ : Container c) {X : Set c} →
            ⟦ C₁ ⊎ C₂ ⟧ X ↔ (⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X)
  correct C₁ C₂ {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
      }
    }
    where
    to : ⟦ C₁ ⊎ C₂ ⟧ X → ⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X
    to (inj₁ s₁ , f) = inj₁ (s₁ , f)
    to (inj₂ s₂ , f) = inj₂ (s₂ , f)

    from : ⟦ C₁ ⟧ X ⟨⊎⟩ ⟦ C₂ ⟧ X → ⟦ C₁ ⊎ C₂ ⟧ X
    from = [ Prod.map inj₁ F.id , Prod.map inj₂ F.id ]

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (inj₁ s₁ , f) = refl
    from∘to (inj₂ s₂ , f) = refl

module IndexedSum where

  correct : ∀ {c I} (C : I → Container c) {X : Set c} →
            ⟦ Σ C ⟧ X ↔ (∃ λ i → ⟦ C i ⟧ X)
  correct {I = I} C {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ Σ C ⟧ X → ∃ λ i → ⟦ C i ⟧ X
    to ((i , s) , f) = (i , (s , f))

    from : (∃ λ i → ⟦ C i ⟧ X) → ⟦ Σ C ⟧ X
    from (i , (s , f)) = ((i , s) , f)

module ConstantExponentiation where

  correct : ∀ {c X} (C : Container c) {Y : Set c} →
            ⟦ const[ X ]⟶ C ⟧ Y ↔ (X → ⟦ C ⟧ Y)
  correct C = IndexedProduct.correct (F.const C)
