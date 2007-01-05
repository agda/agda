
module Category where

import Logic.Identity as Id

open Id using (Identity)
open Id.Projections using (eq)

data Cat : Set2 where
  cat : (Obj  : Set1)
	(_─→_ : Obj -> Obj -> Set)
	(id   : {A : Obj} -> A ─→ A)
	(_∘_	: {A B C : Obj} -> B ─→ C -> A ─→ B -> A ─→ C)
	(Id─→	: {A B : Obj} -> Identity (A ─→ B))
	(idLeft : {A B : Obj}{f : A ─→ B} -> eq Id─→ (id ∘ f) f)
	(idRight : {A B : Obj}{f : A ─→ B} -> eq Id─→ (f ∘ id) f)
	(assoc   : {A B C D : Obj}{f : C ─→ D}{g : B ─→ C}{h : A ─→ B} ->
		   eq Id─→ ((f ∘ g) ∘ h) (f ∘ (g ∘ h))
	) -> Cat

infixr 30 _─→_ _─→'_
infixr 90 _∘_
infix  20 _==_

-- Objects

private
  Obj' : Cat -> Set1
  Obj' (cat o _ _ _ _ _ _ _) = o

data Obj (ℂ : Cat) : Set1 where
  obj : Obj' ℂ -> Obj ℂ

obj⁻¹ : {ℂ : Cat} -> Obj ℂ -> Obj' ℂ
obj⁻¹ (obj A) = A

-- Arrows

private
  _─→'_ : {ℂ : Cat} -> Obj ℂ -> Obj ℂ -> Set
  _─→'_ {cat _ a _ _ _ _ _ _} A B = a (obj⁻¹ A) (obj⁻¹ B)

data _─→_ {ℂ : Cat}(A B : Obj ℂ) : Set where
  arr : A ─→' B -> A ─→ B

arr⁻¹ : {ℂ : Cat}{A B : Obj ℂ} -> A ─→ B -> A ─→' B
arr⁻¹ (arr f) = f

id : {ℂ : Cat}{A : Obj ℂ} -> A ─→ A
id {cat _ _ i _ _ _ _ _} = arr i

_∘_ : {ℂ : Cat}{A B C : Obj ℂ} -> B ─→ C -> A ─→ B -> A ─→ C
_∘_ {cat _ _ _ c _ _ _ _} f g = arr (c (arr⁻¹ f) (arr⁻¹ g))

private
  I : (ℂ : Cat){A B : Obj ℂ} -> Identity (A ─→' B)
  I (cat _ _ _ _ i _ _ _) = i

data _==_ {ℂ : Cat}{A B : Obj ℂ}(f g : A ─→ B) : Set where
  equal : Id.Projections.eq (I ℂ) (arr⁻¹ f) (arr⁻¹ g) -> f == g

EqArr : {ℂ : Cat}{A B : Obj ℂ} -> Identity (A ─→ B)
EqArr {ℂ}{A}{B} = Id.identity _==_ refl subst
  where
    refl : (f : A ─→ B) -> f == f
    refl f = equal (Id.Projections.refl (I ℂ) (arr⁻¹ f))

    subst : (P : A ─→ B -> Set)(f g : A ─→ B) -> f == g -> P f -> P g
    subst P (arr f) (arr g) (equal f=g) Pf = Id.Projections.subst (I ℂ) (\f -> P (arr f)) f g f=g Pf

module PolyEq where
  refl : {ℂ : Cat}{A B : Obj ℂ}{f : A ─→ B} -> f == f
  refl = Id.Projections.refl EqArr _

  subst : {ℂ : Cat}{A B : Obj ℂ}(P : A ─→ B -> Set){f g : A ─→ B} -> f == g -> P f -> P g
  subst P = Id.Projections.subst EqArr P _ _

  cong : {ℂ ⅅ : Cat}{A B : Obj ℂ}{A' B' : Obj ⅅ}(F : A ─→ B -> A' ─→ B')
	 {f g : A ─→ B} -> f == g -> F f == F g
  cong F {f = f} fg = subst (\h -> F f == F h) fg refl

idLeft : {ℂ : Cat}{A B : Obj ℂ}{f : A ─→ B} -> id ∘ f == f
idLeft {cat _ _ _ _ _ l _ _} = equal l

idRight : {ℂ : Cat}{A B : Obj ℂ}{f : A ─→ B} -> f ∘ id == f
idRight {cat _ _ _ _ _ _ r _} = equal r

assoc : {ℂ : Cat}{A B C D : Obj ℂ}{f : C ─→ D}{g : B ─→ C}{h : A ─→ B} ->
	(f ∘ g) ∘ h == f ∘ (g ∘ h)
assoc {cat _ _ _ _ _ _ _ a} = equal a

