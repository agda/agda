------------------------------------------------------------------------
-- A universe which includes both _⇔_ and _⇿_
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Function.Related where

open import Level
open import Function as Fun using (flip)
open import Function.Equivalence as Eq using (Equivalent)
open import Function.Inverse as Inv using (Inverse; _⇿_)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

-- There are two kinds of "relatedness": equivalences and inverses.

data Kind : Set where
  equivalent inverse : Kind

Related : Kind → ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
Related inverse    A B = Inverse    (P.setoid A) (P.setoid B)
Related equivalent A B = Equivalent (P.setoid A) (P.setoid B)

-- Inverses are stronger, equivalences weaker.

⇿⇒ : ∀ {k x y} {X : Set x} {Y : Set y} →
     Related inverse X Y → Related k X Y
⇿⇒ {inverse}    = Fun.id
⇿⇒ {equivalent} = Inverse.equivalent

⇒⇔ : ∀ {k x y} {X : Set x} {Y : Set y} →
     Related k X Y → Related equivalent X Y
⇒⇔ {inverse}    = Inverse.equivalent
⇒⇔ {equivalent} = Fun.id

-- Equational reasoning for related things.

module EquationalReasoning where

  private

    refl : ∀ {k ℓ} → Reflexive (Related k {ℓ})
    refl {inverse}    = Inv.id
    refl {equivalent} = Eq.id

    trans : ∀ {k ℓ₁ ℓ₂ ℓ₃} →
            Trans (Related k {ℓ₁} {ℓ₂})
                  (Related k {ℓ₂} {ℓ₃})
                  (Related k {ℓ₁} {ℓ₃})
    trans {inverse}    = flip Inv._∘_
    trans {equivalent} = flip Eq._∘_

  sym : ∀ {k ℓ₁ ℓ₂} →
        Sym (Related k {ℓ₁} {ℓ₂})
            (Related k {ℓ₂} {ℓ₁})
  sym {inverse}    = Inv.sym
  sym {equivalent} = Eq.sym

  infix  2 _∎
  infixr 2 _≈⟨_⟩_ _⇿⟨_⟩_

  _≈⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           Related k X Y → Related k Y Z → Related k X Z
  _ ≈⟨ X≈Y ⟩ Y≈Z = trans X≈Y Y≈Z

  _⇿⟨_⟩_ : ∀ {k x y z} (X : Set x) {Y : Set y} {Z : Set z} →
           X ⇿ Y → Related k Y Z → Related k X Z
  X ⇿⟨ X⇿Y ⟩ Y⇔Z = X ≈⟨ ⇿⇒ X⇿Y ⟩ Y⇔Z

  _∎ : ∀ {k x} (X : Set x) → Related k X X
  X ∎ = refl

-- For fixed universe levels we can construct a setoid.

setoid : Kind → (ℓ : Level) → Setoid _ _
setoid k ℓ = record
  { Carrier       = Set ℓ
  ; _≈_           = Related k
  ; isEquivalence =
      record {refl = _ ∎; sym = sym; trans = _≈⟨_⟩_ _}
  } where open EquationalReasoning

-- Every unary relation induces an equivalence relation. (No claim is
-- made that this relation is unique.)

InducedEquivalence₁ : Kind → ∀ {a s} {A : Set a}
                      (S : A → Set s) → Setoid _ _
InducedEquivalence₁ k S = record
  { _≈_           = λ x y → Related k (S x) (S y)
  ; isEquivalence = record {refl = refl; sym = sym; trans = trans}
  } where open Setoid (setoid _ _)

-- Every binary relation induces an equivalence relation. (No claim is
-- made that this relation is unique.)

InducedEquivalence₂ : Kind → ∀ {a b s} {A : Set a} {B : Set b}
                      (_S_ : A → B → Set s) → Setoid _ _
InducedEquivalence₂ k _S_ = record
  { _≈_           = λ x y → ∀ {z} → Related k (z S x) (z S y)
  ; isEquivalence = record
    { refl  = refl
    ; sym   = λ i≈j → sym i≈j
    ; trans = λ i≈j j≈k → trans i≈j j≈k
    }
  } where open Setoid (setoid _ _)
