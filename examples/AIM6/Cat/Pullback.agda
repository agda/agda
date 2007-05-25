
module Pullback where

open import Logic.Equivalence
open import Logic.Relations
open import Logic.Base
open import Category
open import Unique

module Pull (ℂ : Cat) where

  private open module CC = Category.Category ℂ
  private open module U = Uniq ℂ

  record isPull {A B C D : Obj}(f : A ─→ B)(g : A ─→ C)(f' : C ─→ D)(g' : B ─→ D) : Set1 where
      A'      : Obj
      h₁      : A' ─→ C
      h₂      : A' ─→ B
      commut  : f' ∘ h₁ == g' ∘ h₂
      unique  : ∃! \(h : A' ─→ A) -> (g ∘ h == h₁) /\ (f ∘ h == h₂)

  record pullback {B C D : Obj}(g' : B ─→ D)(f' : C ─→ D) : Set1 where
      A    : Obj
      f    : A ─→ B
      g    : A ─→ C
      pull : isPull f g f' g'

  record PullCat : Set2 where
    ℂ' : Cat
    pull : {B C D : Obj}(g' : B ─→ D)(f' : C ─→ D) -> pullback g' f'
