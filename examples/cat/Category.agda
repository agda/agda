
module Category where

open import Logic.Equivalence
open import Logic.Relations

data Cat : Set2 where
  cat : (Obj  : Set1)
	(_─→_ : Obj -> Obj -> Set)
	(id   : {A : Obj} -> A ─→ A)
	(_∘_	: {A B C : Obj} -> B ─→ C -> A ─→ B -> A ─→ C)
	(e    : {A B : Obj} -> Equivalence (A ─→ B)) ->
	let _==_ = \{A B : Obj} -> Project-Equivalence.eq (e {A}{B}) in
	(cong : {A B C : Obj}{f₁ f₂ : B ─→ C}{g₁ g₂ : A ─→ B} ->
		f₁ == f₂ -> g₁ == g₂ -> (f₁ ∘ g₁) == (f₂ ∘ g₂)
	)
	(idLeft : {A B : Obj}{f : A ─→ B} -> (id ∘ f) == f)
	(idRight : {A B : Obj}{f : A ─→ B} -> (f ∘ id) == f)
	(assoc   : {A B C D : Obj}{f : C ─→ D}{g : B ─→ C}{h : A ─→ B} ->
		   ((f ∘ g) ∘ h) == (f ∘ (g ∘ h))
	) -> Cat

module Project-Cat where

  Obj : Cat -> Set1
  Obj (cat o _ _ _ _ _ _ _ _) = o

  Arr : (ℂ : Cat) -> Obj ℂ -> Obj ℂ -> Set
  Arr (cat _ a _ _ _ _ _ _ _) = a

  id : (ℂ : Cat){A : Obj ℂ} -> Arr ℂ A A
  id (cat _ _ i _ _ _ _ _ _) = i

  compose : (ℂ : Cat){A B C : Obj ℂ} ->  Arr ℂ B C -> Arr ℂ A B -> Arr ℂ A C
  compose (cat _ _ _ c _ _ _ _ _) = c

  Eq : (ℂ : Cat){A B : Obj ℂ} -> Equivalence (Arr ℂ A B)
  Eq (cat _ _ _ _ e _ _ _ _) = e

  equal : (ℂ : Cat){A B : Obj ℂ} -> Rel (Arr ℂ A B)
  equal ℂ = Project-Equivalence.eq (Eq ℂ)

  refl : (ℂ : Cat){A B : Obj ℂ}{f : Arr ℂ A B} -> equal ℂ f f
  refl ℂ = Project-Equivalence.refl (Eq ℂ) _

  sym : (ℂ : Cat){A B : Obj ℂ}{f g : Arr ℂ A B} -> equal ℂ f g -> equal ℂ g f
  sym ℂ = Project-Equivalence.sym (Eq ℂ) _ _

  trans : (ℂ : Cat){A B : Obj ℂ}{f g h : Arr ℂ A B} ->
	  equal ℂ f g -> equal ℂ g h -> equal ℂ f h
  trans ℂ = Project-Equivalence.trans (Eq ℂ) _ _ _

  cong : (ℂ : Cat){A B C : Obj ℂ}{f₁ f₂ : Arr ℂ B C}{g₁ g₂ : Arr ℂ A B} ->
	 equal ℂ f₁ f₂ -> equal ℂ g₁ g₂ -> equal ℂ (compose ℂ f₁ g₁) (compose ℂ f₂ g₂)
  cong (cat _ _ _ _ _ c _ _ _) = c

  congL : (ℂ : Cat){A B C : Obj ℂ}{f₁ f₂ : Arr ℂ B C}{g : Arr ℂ A B} ->
	  equal ℂ f₁ f₂ -> equal ℂ (compose ℂ f₁ g) (compose ℂ f₂ g)
  congL ℂ p = cong ℂ p (refl ℂ)

  congR : (ℂ : Cat){A B C : Obj ℂ}{f : Arr ℂ B C}{g₁ g₂ : Arr ℂ A B} ->
	  equal ℂ g₁ g₂ -> equal ℂ (compose ℂ f g₁) (compose ℂ f g₂)
  congR ℂ p = cong ℂ (refl ℂ) p

  idL : (ℂ : Cat){A B : Obj ℂ}{f : Arr ℂ A B} -> equal ℂ (compose ℂ (id ℂ) f) f
  idL (cat _ _ _ _ _ _ l _ _) = l

  idR : (ℂ : Cat){A B : Obj ℂ}{f : Arr ℂ A B} -> equal ℂ (compose ℂ f (id ℂ)) f
  idR (cat _ _ _ _ _ _ _ r _) = r

  assoc : (ℂ : Cat){A B C D : Obj ℂ}
	  {f : Arr ℂ C D}{g : Arr ℂ B C}{h : Arr ℂ A B} ->
	  equal ℂ (compose ℂ (compose ℂ f g) h)
		  (compose ℂ f (compose ℂ g h))
  assoc (cat _ _ _ _ _ _ _ _ a) = a

module Cat (ℂ : Cat) where

  infix	 20 _==_
  infixr 30 _─→_
  infixr 90 _∘_

  private module Pr = Project-Cat

  Obj : Set1
  Obj = Pr.Obj ℂ

  _─→_ : Obj -> Obj -> Set
  A ─→ B = Pr.Arr ℂ A B

  id : {A : Obj} -> A ─→ A
  id = Pr.id ℂ

  _∘_ : {A B C : Obj} -> B ─→ C -> A ─→ B -> A ─→ C
  f ∘ g = Pr.compose ℂ f g

  Eq : {A B : Obj} -> Equivalence (A ─→ B)
  Eq = Pr.Eq ℂ

  _==_ : {A B : Obj} -> Rel (A ─→ B)
  f == g = Pr.equal ℂ f g

  refl : {A B : Obj}{f : A ─→ B} -> f == f
  refl = Pr.refl ℂ

  sym : {A B : Obj}{f g : A ─→ B} -> f == g -> g == f
  sym = Pr.sym ℂ

  trans : {A B : Obj}{f g h : A ─→ B} ->
	  f == g -> g == h -> f == h
  trans = Pr.trans ℂ

  cong : {A B C : Obj}{f₁ f₂ : B ─→ C}{g₁ g₂ : A ─→ B} ->
	 f₁ == f₂ -> g₁ == g₂ -> f₁ ∘ g₁ == f₂ ∘ g₂
  cong = Pr.cong ℂ

  congL : {A B C : Obj}{f₁ f₂ : B ─→ C}{g : A ─→ B} ->
	  f₁ == f₂ -> f₁ ∘ g == f₂ ∘ g
  congL = Pr.congL ℂ

  congR : {A B C : Obj}{f : B ─→ C}{g₁ g₂ : A ─→ B} ->
	  g₁ == g₂ -> f ∘ g₁ == f ∘ g₂
  congR = Pr.congR ℂ

  idL : {A B : Obj}{f : A ─→ B} -> id ∘ f == f
  idL = Pr.idL ℂ

  idR : {A B : Obj}{f : A ─→ B} -> f ∘ id == f
  idR = Pr.idR ℂ

  assoc : {A B C D : Obj}{f : C ─→ D}{g : B ─→ C}{h : A ─→ B} ->
	  (f ∘ g) ∘ h == f ∘ (g ∘ h)
  assoc = Pr.assoc ℂ

-- Manual η-expansion of a category.
η-Cat : Cat -> Cat
η-Cat ℂ = cat Obj _─→_ id _∘_ Eq cong idL idR assoc
  where open module C = Cat ℂ

module Poly-Cat where

  infix  20 _==_
  infixr 30 _─→_ _─→'_
  infixr 90 _∘_

  private module Pr = Project-Cat

  -- Objects
  data Obj (ℂ : Cat) : Set1 where
    obj : Pr.Obj ℂ -> Obj ℂ

  obj⁻¹ : {ℂ : Cat} -> Obj ℂ -> Pr.Obj ℂ
  obj⁻¹ (obj A) = A

  -- Arrows
  data _─→_ {ℂ : Cat}(A B : Obj ℂ) : Set where
    arr : Pr.Arr ℂ (obj⁻¹ A) (obj⁻¹ B) -> A ─→ B

  arr⁻¹ : {ℂ : Cat}{A B : Obj ℂ} -> A ─→ B -> Pr.Arr ℂ (obj⁻¹ A) (obj⁻¹ B)
  arr⁻¹ (arr f) = f

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

