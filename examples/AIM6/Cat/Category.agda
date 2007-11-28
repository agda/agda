
module Category where

open import Logic.Equivalence
open import Logic.Relations

open Equivalence using () renaming (_==_ to eq)

record Cat : Set2 where
  field
    Obj     : Set1
    _─→_    : Obj -> Obj -> Set
    id      : {A : Obj} -> A ─→ A
    _∘_     : {A B C : Obj} -> B ─→ C -> A ─→ B -> A ─→ C
    Eq      : {A B : Obj} -> Equivalence (A ─→ B)
    cong    : {A B C : Obj}{f₁ f₂ : B ─→ C}{g₁ g₂ : A ─→ B} ->
              eq Eq f₁ f₂ -> eq Eq g₁ g₂ -> eq Eq (f₁ ∘ g₁) (f₂ ∘ g₂)
    idLeft  : {A B : Obj}{f : A ─→ B} -> eq Eq (id ∘ f) f
    idRight : {A B : Obj}{f : A ─→ B} -> eq Eq (f ∘ id) f
    assoc   : {A B C D : Obj}{f : C ─→ D}{g : B ─→ C}{h : A ─→ B} ->
              eq Eq ((f ∘ g) ∘ h) (f ∘ (g ∘ h))

module Category (ℂ : Cat) where

  private module CC = Cat ℂ
  open CC public hiding (_─→_; _∘_)

  private module Eq {A B : Obj} = Equivalence (Eq {A}{B})
  open Eq public hiding (_==_)

  infix	 20 _==_
  infixr 30 _─→_
  infixr 90 _∘_

  _─→_ = CC._─→_

  _==_ : {A B : Obj} -> Rel (A ─→ B)
  _==_ = Eq._==_

  _∘_ : {A B C : Obj} -> B ─→ C -> A ─→ B -> A ─→ C
  _∘_ = CC._∘_

  congL : {A B C : Obj}{f₁ f₂ : B ─→ C}{g : A ─→ B} ->
	  f₁ == f₂ -> f₁ ∘ g == f₂ ∘ g
  congL p = cong p refl

  congR : {A B C : Obj}{f : B ─→ C}{g₁ g₂ : A ─→ B} ->
	  g₁ == g₂ -> f ∘ g₁ == f ∘ g₂
  congR p = cong refl p
