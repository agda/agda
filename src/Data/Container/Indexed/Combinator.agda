------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed container combinators
------------------------------------------------------------------------

module Data.Container.Indexed.Combinator where

open import Level
open import Data.Container.Indexed
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Minimal using (⊤)
open import Data.Product as Prod hiding (Σ) renaming (_×_ to _⟨×⟩_)
open import Data.Sum renaming (_⊎_ to _⟨⊎⟩_)
open import Function as F hiding (id; const) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse using (_↔̇_)
open import Relation.Unary using (Pred; _⊆_; _∪_; _∩_; ⋃; ⋂)
  renaming (_⟨×⟩_ to _⟪×⟫_; _⟨⊙⟩_ to _⟪⊙⟫_; _⟨⊎⟩_ to _⟪⊎⟫_)
open import Relation.Binary.PropositionalEquality as P
  using (_≗_; refl)

------------------------------------------------------------------------
-- Combinators


-- Identity.

id : ∀ {o c r} {O : Set o} → Container O O c r
id = F.const (Lift ⊤) ◃ (λ _ → Lift ⊤) / (λ {o} _ _ → o)

-- Constant.

const : ∀ {i o c r} {I : Set i} {O : Set o} →
        Pred O c → Container I O c r
const X = X ◃ (λ _ → Lift ⊥) / λ _ → ⊥-elim ⟨∘⟩ lower

-- Duality.

_^⊥ : ∀ {i o c r} {I : Set i} {O : Set o} →
      Container I O c r → Container I O (c ⊔ r) c
(C ◃ R / n) ^⊥ = record
  { Command  = λ o → (c : C o) → R c
  ; Response = λ {o} _ → C o
  ; next     = λ f c → n c (f c)
  }

-- Strength.

infixl 3 _⋊_

_⋊_ : ∀ {i o c r z} {I : Set i} {O : Set o} (C : Container I O c r)
      (Z : Set z) → Container (I ⟨×⟩ Z) (O ⟨×⟩ Z) c r
C ◃ R / n ⋊ Z = C ⟨∘⟩ proj₁ ◃ R / λ {oz} c r → n c r , proj₂ oz

infixr 3 _⋉_

_⋉_ : ∀ {i o z c r} {I : Set i} {O : Set o} (Z : Set z)
      (C : Container I O c r) → Container (Z ⟨×⟩ I) (Z ⟨×⟩ O) c r
Z ⋉ C ◃ R / n = C ⟨∘⟩ proj₂ ◃ R / λ {zo} c r → proj₁ zo , n c r

-- Composition.

infixr 9 _∘_

_∘_ : ∀ {i j k c r} {I : Set i} {J : Set j} {K : Set k} →
      Container J K c r → Container I J c r → Container I K _ _
C₁ ∘ C₂ = C ◃ R / n
  where
  C : ∀ k → Set _
  C = ⟦ C₁ ⟧ (Command C₂)

  R : ∀ {k} → ⟦ C₁ ⟧ (Command C₂) k → Set _
  R (c , k) = ◇ C₁ {X = Command C₂} (Response C₂ ⟨∘⟩ proj₂) (_ , c , k)

  n : ∀ {k} (c : ⟦ C₁ ⟧ (Command C₂) k) → R c → _
  n (_ , f) (r₁ , r₂) = next C₂ (f r₁) r₂

-- Product. (Note that, up to isomorphism, this is a special case of
-- indexed product.)

infixr 2 _×_

_×_ : ∀ {i o c r} {I : Set i} {O : Set o} →
      Container I O c r → Container I O c r → Container I O c r
(C₁ ◃ R₁ / n₁) × (C₂ ◃ R₂ / n₂) = record
  { Command  = C₁ ∩ C₂
  ; Response = R₁ ⟪⊙⟫ R₂
  ; next     = λ { (c₁ , c₂) → [ n₁ c₁ , n₂ c₂ ] }
  }

-- Indexed product.

Π : ∀ {x i o c r} {X : Set x} {I : Set i} {O : Set o} →
    (X → Container I O c r) → Container I O _ _
Π {X = X} C = record
  { Command  = ⋂ X (Command ⟨∘⟩ C)
  ; Response = ⋃[ x ∶ X ] λ c → Response (C x) (c x)
  ; next     = λ { c (x , r) → next (C x) (c x) r }
  }

-- Sum. (Note that, up to isomorphism, this is a special case of
-- indexed sum.)

infixr 1 _⊎_

_⊎_ : ∀ {i o c r} {I : Set i} {O : Set o} →
      Container I O c r → Container I O c r → Container I O _ _
(C₁ ◃ R₁ / n₁) ⊎ (C₂ ◃ R₂ / n₂) = record
  { Command  = C₁ ∪ C₂
  ; Response = R₁ ⟪⊎⟫ R₂
  ; next     = [ n₁ , n₂ ]
  }

-- Indexed sum.

Σ : ∀ {x i o c r} {X : Set x} {I : Set i} {O : Set o} →
    (X → Container I O c r) → Container I O _ r
Σ {X = X} C = record
  { Command  = ⋃ X (Command ⟨∘⟩ C)
  ; Response = λ { (x , c) → Response (C x) c }
  ; next     = λ { (x , c) r → next (C x) c r }
  }

-- Constant exponentiation. (Note that this is a special case of
-- indexed product.)

infix 0 const[_]⟶_

const[_]⟶_ : ∀ {i o c r ℓ} {I : Set i} {O : Set o} →
             Set ℓ → Container I O c r → Container I O _ _
const[ X ]⟶ C = Π {X = X} (F.const C)

------------------------------------------------------------------------
-- Correctness proofs

module Identity where

  correct : ∀ {o ℓ c r} {O : Set o} {X : Pred O ℓ} →
            ⟦ id {c = c}{r} ⟧ X ↔̇ F.id X
  correct = record
    { to         = P.→-to-⟶ λ xs → proj₂ xs _
    ; from       = P.→-to-⟶ λ x → (_ , λ _ → x)
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }

module Constant (ext : ∀ {ℓ} → P.Extensionality ℓ ℓ) where

  correct : ∀ {i o ℓ₁ ℓ₂} {I : Set i} {O : Set o} (X : Pred O ℓ₁)
            {Y : Pred O ℓ₂} → ⟦ const X ⟧ Y ↔̇ F.const X Y
  correct X {Y} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { right-inverse-of = λ _ → refl
      ; left-inverse-of  =
          λ xs → P.cong (_,_ (proj₁ xs)) (ext (⊥-elim ⟨∘⟩ lower))
      }
    }
    where
    to : ⟦ const X ⟧ Y ⊆ X
    to = proj₁

    from : X ⊆ ⟦ const X ⟧ Y
    from = < F.id , F.const (⊥-elim ⟨∘⟩ lower) >

module Duality where

  correct : ∀ {i o c r ℓ} {I : Set i} {O : Set o}
              (C : Container I O c r) (X : Pred I ℓ) →
            ⟦ C ^⊥ ⟧ X ↔̇ (λ o → (c : Command C o) → ∃ λ r → X (next C c r))
  correct C X = record
    { to         = P.→-to-⟶ λ { (f , g) → < f , g > }
    ; from       = P.→-to-⟶ λ f → proj₁ ⟨∘⟩ f , proj₂ ⟨∘⟩ f
    ; inverse-of = record
      { left-inverse-of  = λ { (_ , _) → refl }
      ; right-inverse-of = λ _ → refl
      }
    }

module Composition where

  correct : ∀ {i j k ℓ c r} {I : Set i} {J : Set j} {K : Set k}
              (C₁ : Container J K c r) (C₂ : Container I J c r) →
            {X : Pred I ℓ} → ⟦ C₁ ∘ C₂ ⟧ X ↔̇ (⟦ C₁ ⟧ ⟨∘⟩ ⟦ C₂ ⟧) X
  correct C₁ C₂ {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ C₁ ∘ C₂ ⟧ X ⊆ ⟦ C₁ ⟧ (⟦ C₂ ⟧ X)
    to ((c , f) , g) = (c , < f , curry g >)

    from : ⟦ C₁ ⟧ (⟦ C₂ ⟧ X) ⊆ ⟦ C₁ ∘ C₂ ⟧ X
    from (c , f) = ((c , proj₁ ⟨∘⟩ f) , uncurry (proj₂ ⟨∘⟩ f))

module Product (ext : ∀ {ℓ} → P.Extensionality ℓ ℓ) where

  correct : ∀ {i o c r} {I : Set i} {O : Set o}
              (C₁ C₂ : Container I O c r) {X} →
            ⟦ C₁ × C₂ ⟧ X ↔̇ (⟦ C₁ ⟧ X ∩ ⟦ C₂ ⟧ X)
  correct C₁ C₂ {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ C₁ × C₂ ⟧ X ⊆ ⟦ C₁ ⟧ X ∩ ⟦ C₂ ⟧ X
    to ((c₁ , c₂) , k) = ((c₁ , k ⟨∘⟩ inj₁) , (c₂ , k ⟨∘⟩ inj₂))

    from : ⟦ C₁ ⟧ X ∩ ⟦ C₂ ⟧ X ⊆ ⟦ C₁ × C₂ ⟧ X
    from ((c₁ , k₁) , (c₂ , k₂)) = ((c₁ , c₂) , [ k₁ , k₂ ])

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (c , _) =
      P.cong (_,_ c) (ext [ (λ _ → refl) , (λ _ → refl) ])

module IndexedProduct where

  correct : ∀ {x i o c r ℓ} {X : Set x} {I : Set i} {O : Set o}
              (C : X → Container I O c r) {Y : Pred I ℓ} →
            ⟦ Π C ⟧ Y ↔̇ ⋂[ x ∶ X ] ⟦ C x ⟧ Y
  correct {X = X} C {Y} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ Π C ⟧ Y ⊆ ⋂[ x ∶ X ] ⟦ C x ⟧ Y
    to (c , k) = λ x → (c x , λ r → k (x , r))

    from : ⋂[ x ∶ X ] ⟦ C x ⟧ Y ⊆ ⟦ Π C ⟧ Y
    from f = (proj₁ ⟨∘⟩ f , uncurry (proj₂ ⟨∘⟩ f))

module Sum where

  correct : ∀ {i o c r ℓ} {I : Set i} {O : Set o}
              (C₁ C₂ : Container I O c r) {X : Pred I ℓ} →
            ⟦ C₁ ⊎ C₂ ⟧ X ↔̇ (⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X)
  correct C₁ C₂ {X} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = [ (λ _ → refl) , (λ _ → refl) ]
      }
    }
    where
    to : ⟦ C₁ ⊎ C₂ ⟧ X ⊆ ⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X
    to (inj₁ c₁ , k) = inj₁ (c₁ , k)
    to (inj₂ c₂ , k) = inj₂ (c₂ , k)

    from : ⟦ C₁ ⟧ X ∪ ⟦ C₂ ⟧ X ⊆ ⟦ C₁ ⊎ C₂ ⟧ X
    from = [ Prod.map inj₁ F.id , Prod.map inj₂ F.id ]

    from∘to : from ⟨∘⟩ to ≗ F.id
    from∘to (inj₁ _ , _) = refl
    from∘to (inj₂ _ , _) = refl

module IndexedSum where

  correct : ∀ {x i o c r ℓ} {X : Set x} {I : Set i} {O : Set o}
              (C : X → Container I O c r) {Y : Pred I ℓ} →
            ⟦ Σ C ⟧ Y ↔̇ ⋃[ x ∶ X ] ⟦ C x ⟧ Y
  correct {X = X} C {Y} = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ _ → refl
      ; right-inverse-of = λ _ → refl
      }
    }
    where
    to : ⟦ Σ C ⟧ Y ⊆ ⋃[ x ∶ X ] ⟦ C x ⟧ Y
    to ((x , c) , k) = (x , (c , k))

    from : ⋃[ x ∶ X ] ⟦ C x ⟧ Y ⊆ ⟦ Σ C ⟧ Y
    from (x , (c , k)) = ((x , c) , k)

module ConstantExponentiation where

  correct : ∀ {x i o c r ℓ} {X : Set x} {I : Set i} {O : Set o}
              (C : Container I O c r) {Y : Pred I ℓ} →
            ⟦ const[ X ]⟶ C ⟧ Y ↔̇ (⋂ X (F.const (⟦ C ⟧ Y)))
  correct C {Y} = IndexedProduct.correct (F.const C) {Y}
