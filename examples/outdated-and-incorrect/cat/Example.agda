
module Example where

open import Logic.Identity
open import Base
open import Category
open import Product
open import Terminal
open import Unique
import Iso

infixr 30 _─→_
infixr 90 _∘_

data Name : Set where
  Zero : Name
  One  : Name
  Half : Name

data Obj : Set1 where
  obj : Name -> Obj

mutual
  _─→'_ : Name -> Name -> Set
  x ─→' y = obj x ─→ obj y

  data _─→_ : Obj -> Obj -> Set where
    Idle  : {A : Name} -> A    ─→' A
    All   :		  Zero ─→' One
    Start :		  Zero ─→' Half
    Turn  :		  Half ─→' Half
    Back  :		  One  ─→' Half
    End   :		  Half ─→' One

id : {A : Obj} -> A ─→ A
id {obj x} = Idle

_∘_ : {A B C : Obj} -> B ─→ C -> A ─→ B -> A ─→ C
f    ∘ Idle  = f
Idle ∘ All   = All
Idle ∘ Start = Start
Turn ∘ Start = Start
End  ∘ Start = All
Idle ∘ Turn  = Turn
Turn ∘ Turn  = Turn
End  ∘ Turn  = End
Idle ∘ Back  = Back
Turn ∘ Back  = Back
End  ∘ Back  = Idle
Idle ∘ End   = End

idL : {A B : Obj}{f : A ─→ B} -> id ∘ f ≡ f
idL {f = Idle  } = refl
idL {f = All   } = refl
idL {f = Start } = refl
idL {f = Turn  } = refl
idL {f = Back  } = refl
idL {f = End   } = refl

idR : {A B : Obj}{f : A ─→ B} -> f ∘ id ≡ f
idR {obj _} = refl

assoc : {A B C D : Obj}{f : C ─→ D}{g : B ─→ C}{h : A ─→ B} ->
	(f ∘ g) ∘ h ≡ f ∘ (g ∘ h)
assoc {f = _   }{g = _   }{h = Idle } = refl
assoc {f = _   }{g = Idle}{h = All  } = refl
assoc {f = _   }{g = Idle}{h = Start} = refl
assoc {f = Idle}{g = Turn}{h = Start} = refl
assoc {f = Turn}{g = Turn}{h = Start} = refl
assoc {f = End }{g = Turn}{h = Start} = refl
assoc {f = Idle}{g = End }{h = Start} = refl
assoc {f = _   }{g = Idle}{h = Turn } = refl
assoc {f = Idle}{g = Turn}{h = Turn } = refl
assoc {f = Turn}{g = Turn}{h = Turn } = refl
assoc {f = End }{g = Turn}{h = Turn } = refl
assoc {f = Idle}{g = End }{h = Turn } = refl
assoc {f = _   }{g = Idle}{h = Back } = refl
assoc {f = Idle}{g = Turn}{h = Back } = refl
assoc {f = Turn}{g = Turn}{h = Back } = refl
assoc {f = End }{g = Turn}{h = Back } = refl
assoc {f = Idle}{g = End }{h = Back } = refl
assoc {f = _   }{g = Idle}{h = End  } = refl

ℂ : Cat
ℂ = cat Obj _─→_ id _∘_
	(\{_}{_} -> Equiv)
	(\{_}{_}{_} -> cong2 _∘_)
	idL idR assoc

open module T = Term ℂ
open module I = Init ℂ
open module S = Sum ℂ

term : Terminal (obj One)
term (obj Zero) = ?

init : Initial (obj Zero)
init = ?


