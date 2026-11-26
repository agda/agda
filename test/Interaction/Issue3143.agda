-- Andreas, 2026-11-26, issue #3143, report and reproducer by Jesper Cockx
-- Type inference failure with irrelevant levels.
-- Fixed in 2.6.2.

{-# OPTIONS --experimental-irrelevance #-}

open import Agda.Primitive

record _×_ .{i j : Level} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_

record Cat .(i j : Level) : Set (lsuc (i ⊔ j)) where
  field
    Ob   : Set i
    Hom  : Ob → Ob → Set j
open Cat

record Functor .{i₁ i₂ j₁ j₂ : Level} (C₁ : Cat i₁ j₁) (C₂ : Cat i₂ j₂) : Set (i₁ ⊔ i₂ ⊔ j₁ ⊔ j₂) where
  field
    Ob  : C₁ .Ob → C₂ .Ob
    Hom : ∀ {X Y} → C₁ .Hom X Y → C₂ .Hom (Ob X) (Ob Y)
open Functor

record NaturalT .{i₁ i₂ j₁ j₂ : Level} {C₁ : Cat i₁ j₁} {C₂ : Cat i₂ j₂} (F G : Functor C₁ C₂) : Set (i₁ ⊔ j₁ ⊔ j₂) where
  field
    component : {X : C₁ .Ob} → C₂ .Hom (F .Ob X) (G .Ob X)
open NaturalT

record Exponentials .{i j : Level} (C : Cat i j) (prod : C .Ob → C .Ob → C .Ob) : Set (i ⊔ j) where
  field
    fun    : C .Ob → C .Ob → C .Ob
    eval   : ∀ {X Y} → C .Hom (prod (fun X Y) X) Y
open Exponentials

module _ ..(i j : Level) where
  Cats : Cat (lsuc i ⊔ lsuc j) (i ⊔ j)
  Cats .Ob      = Cat i j
  Cats .Hom X Y = Functor X Y

module _ .{i₁ j₁ i₂ j₂} (C₁ : Cat i₁ j₁) (C₂ : Cat i₂ j₂) where
  Pairs : Cat (i₁ ⊔ i₂) (j₁ ⊔ j₂)
  Pairs .Ob = C₁ .Ob × C₂ .Ob
  Pairs .Hom (X₁ , X₂) (Y₁ , Y₂) = C₁ .Hom X₁ Y₁ × C₂ .Hom X₂ Y₂

  Functors : Cat (i₁ ⊔ i₂ ⊔ j₁ ⊔ j₂) (i₁ ⊔ j₁ ⊔ j₂)
  Functors .Ob       = Functor C₁ C₂
  Functors .Hom F G  = NaturalT F G

exponentialCat : .(i j : Level) → Exponentials (Cats i j) Pairs
exponentialCat i j = λ where
  .fun C₁ C₂ → Functors C₁ C₂
  .eval .Ob  (F , X) → F .Ob X
  .eval .Hom (T , f) → {!T .component!}  -- C-c C-d

-- Inferring `T .component` gave error
-- Set j != Set (i ⊔ j)
-- when checking that the expression T has type
-- NaturalT (π₁ .X₁) (π₁ .Y₁)

-- Should succeed
