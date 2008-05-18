
module Pullback where

open import Logic.Equivalence
open import Logic.Relations
open import Logic.Base
open import Category
open import Unique

module Pull (ℂ : Cat) where

  private open module CC = Category.Category ℂ
  private open module U = Uniq ℂ

  record isPull {A B C D A' : Obj}(f : A ─→ B)(g : A ─→ C)(f' : C ─→ D)(g' : B ─→ D)(h₁ : A' ─→ C)(h₂ : A' ─→ B)(commut : f' ∘ h₁ == g' ∘ h₂) : Set1 where
    field unique  : ∃! \(h : A' ─→ A) -> (g ∘ h == h₁) /\ (f ∘ h == h₂)

  record pullback {B C D : Obj}(g' : B ─→ D)(f' : C ─→ D) : Set1 where
    field
      A    : Obj
      f    : A ─→ B
      g    : A ─→ C
      comm : g' ∘ f == f' ∘ g
      pull : (forall {A' : Obj}(h₁ : A' ─→ C)(h₂ : A' ─→ B)(commut : f' ∘ h₁ == g' ∘ h₂) -> isPull f g f' g' h₁ h₂ commut)

  record PullCat : Set2 where
    field pull : {B C D : Obj}(g' : B ─→ D)(f' : C ─→ D) -> pullback g' f'
