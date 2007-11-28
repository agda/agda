
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
  congL p = cong p (refl _)

  congR : {A B C : Obj}{f : B ─→ C}{g₁ g₂ : A ─→ B} ->
	  g₁ == g₂ -> f ∘ g₁ == f ∘ g₂
  congR p = cong (refl _) p

module Poly-Cat where

  infix  20 _==_
  infixr 30 _─→_ _─→'_
  infixr 90 _∘_

  private module C = Category

  -- Objects
  data Obj (ℂ : Cat) : Set1 where
--     obj : C.Obj ℂ -> Obj ℂ

--   obj⁻¹ : {ℂ : Cat} -> Obj ℂ -> C.Obj ℂ
--   obj⁻¹ {ℂ} (obj A) = A

  postulate X : Set

  -- Arrows
  data _─→_ {ℂ : Cat}(A B : Obj ℂ) : Set where
    arr : X -> A ─→ B -- C._─→_ ℂ (obj⁻¹ A) (obj⁻¹ B) -> A ─→ B


  postulate
    ℂ : Cat
    A : Obj ℂ
    B : Obj ℂ

  foo : A ─→ B -> X
  foo (arr f) = ?

--   arr⁻¹ : {ℂ : Cat}{A B : Obj ℂ} -> A ─→ B -> C._─→_ ℂ (obj⁻¹ A) (obj⁻¹ B)
--   arr⁻¹ {ℂ}{A}{B} (arr f) = f

open Poly-Cat
open Category hiding (Obj; _─→_)

{-
  id : {ℂ : Cat}{A : Obj ℂ} -> A ─→ A
  id {ℂ} = arr (Pr.id ℂ)

  _∘_ : {ℂ : Cat}{A B C : Obj ℂ} -> B ─→ C -> A ─→ B -> A ─→ C
  _∘_ {ℂ} (arr f) (arr g) = arr (Pr.compose ℂ f g)

  data _==_ {ℂ : Cat}{A B : Obj ℂ}(f g : A ─→ B) : Set where
    eqArr : Pr.equal ℂ (arr⁻¹ f) (arr⁻¹ g) -> f == g

  refl : {ℂ : Cat}{A B : Obj ℂ}{f : A ─→ B} -> f == f
  refl {ℂ} = eqArr (Pr.refl ℂ)

  sym : {ℂ : Cat}{A B : Obj ℂ}{f g : A ─→ B} -> f == g -> g == f
  sym {ℂ} (eqArr fg) = eqArr (Pr.sym ℂ fg)

  trans : {ℂ : Cat}{A B : Obj ℂ}{f g h : A ─→ B} -> f == g -> g == h -> f == h
  trans {ℂ} (eqArr fg) (eqArr gh) = eqArr (Pr.trans ℂ fg gh)

  cong : {ℂ : Cat}{A B C : Obj ℂ}{f₁ f₂ : B ─→ C}{g₁ g₂ : A ─→ B} ->
	 f₁ == f₂ -> g₁ == g₂ -> f₁ ∘ g₁ == f₂ ∘ g₂
  cong {ℂ} {f₁ = arr _}{f₂ = arr _}{g₁ = arr _}{g₂ = arr _}
	   (eqArr p) (eqArr q) = eqArr (Pr.cong ℂ p q)

  congL : {ℂ : Cat}{A B C : Obj ℂ}{f₁ f₂ : B ─→ C}{g : A ─→ B} ->
	  f₁ == f₂ -> f₁ ∘ g == f₂ ∘ g
  congL p = cong p refl

  congR : {ℂ : Cat}{A B C : Obj ℂ}{f : B ─→ C}{g₁ g₂ : A ─→ B} ->
	  g₁ == g₂ -> f ∘ g₁ == f ∘ g₂
  congR q = cong refl q

  Eq : {ℂ : Cat}{A B : Obj ℂ} -> Equivalence (A ─→ B)
  Eq = equiv _==_ (\x -> refl) (\x y -> sym) (\x y z -> trans)

  idL : {ℂ : Cat}{A B : Obj ℂ}{f : A ─→ B} -> id ∘ f == f
  idL {ℂ}{f = arr _} = eqArr (Pr.idL ℂ)

  idR : {ℂ : Cat}{A B : Obj ℂ}{f : A ─→ B} -> f ∘ id == f
  idR {ℂ}{f = arr _} = eqArr (Pr.idR ℂ)

  assoc : {ℂ : Cat}{A B C D : Obj ℂ}{f : C ─→ D}{g : B ─→ C}{h : A ─→ B} ->
	  (f ∘ g) ∘ h == f ∘ (g ∘ h)
  assoc {ℂ}{f = arr _}{g = arr _}{h = arr _} = eqArr (Pr.assoc ℂ)
-}

