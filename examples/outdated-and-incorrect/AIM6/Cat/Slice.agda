
module Slice where

open import Logic.Relations
open import Logic.Equivalence
open import Logic.Base
open import Category

module SliceCat (ℂ : Cat)(Γ : Category.Obj ℂ) where

  open module CC = Category.Category ℂ


  record SlObj : Set1 where
    field
      dom : Obj
      arr : dom ─→ Γ 

  record _Sl→_ (f f' : SlObj) : Set where
    field
      h : (SlObj.dom f) ─→ (SlObj.dom f')
      π : (SlObj.arr f') ∘ h == (SlObj.arr f)

  SlId : {f : SlObj} -> f Sl→ f
  SlId = record
    { h = id
    ; π = idRight
    }

  _o_ : {f f' f'' : SlObj} -> f' Sl→ f'' -> f Sl→ f' -> f Sl→ f''
  _o_ {F} {F'} {F''} F₁ F₂ = 
    let f   = SlObj.arr F   in 
    let f'  = SlObj.arr F'  in 
    let f'' = SlObj.arr F'' in 
    let h'  = _Sl→_.h F₁     in 
    let h   = _Sl→_.h F₂     in 
    record
      { h = (_Sl→_.h F₁) ∘ (_Sl→_.h F₂)
      -- Proof of f'' ∘ (h' ∘ h) == f
      ; π = trans (trans (sym assoc) 
                         (congL (_Sl→_.π F₁)))
                  (_Sl→_.π F₂)
      }

  SlRel : {A B : SlObj} -> Rel (A Sl→ B)
  SlRel f f' = (_Sl→_.h f) == (_Sl→_.h f')

  SlRefl : {A B : SlObj} -> Reflexive {A Sl→ B} SlRel
  SlRefl = refl 

  SlSym : {A B : SlObj} -> Symmetric {A Sl→ B} SlRel
  SlSym = sym 

  SlTrans : {A B : SlObj} -> Transitive {A Sl→ B} SlRel
  SlTrans = trans 

  SlEq : {A B : SlObj} -> Equivalence (A Sl→ B)
  SlEq {A} {B} = record 
    { _==_  = SlRel {A} {B}
    ; refl  = \{f     : A Sl→ B} -> SlRefl  {A}{B}{f}
    ; sym   = \{f g   : A Sl→ B} -> SlSym   {A}{B}{f}{g}
    ; trans = \{f g h : A Sl→ B} -> SlTrans {A}{B}{f}{g}{h}
    }

  SlCong : {A B C : SlObj}{f f' : B Sl→ C}{g g' : A Sl→ B} ->
    SlRel f f' -> SlRel g g' -> SlRel (f o g) (f' o g')
  SlCong = cong

  SlIdLeft : {A B : SlObj}{f : A Sl→ B} -> SlRel (SlId o f) f
  SlIdLeft = idLeft

  SlIdRight : {A B : SlObj}{f : A Sl→ B} -> SlRel (f o SlId) f
  SlIdRight = idRight

  SlAssoc : {A B C D : SlObj}{f : C Sl→ D}{g : B Sl→ C}{h : A Sl→ B} ->
    SlRel ((f o g) o h) (f o (g o h))
  SlAssoc = assoc

  Slice : Cat
  Slice = record
    { Obj     = SlObj
    ; _─→_    = _Sl→_
    ; id      = SlId
    ; _∘_     = _o_
    ; Eq      = SlEq
    ; cong    = \{A B C : SlObj}{f f' : B Sl→ C}{g g' : A Sl→ B} -> SlCong {A}{B}{C}{f}{f'}{g}{g'}
    ; idLeft  = \{A B : SlObj}{f : A Sl→ B} -> SlIdLeft {A} {B} {f}
    ; idRight = \{A B : SlObj}{f : A Sl→ B} -> SlIdRight {A} {B} {f}
    ; assoc   = \{A B C D : SlObj}{f : C Sl→ D}{g : B Sl→ C}{h : A Sl→ B} -> 
        SlAssoc {A}{B}{C}{D}{f}{g}{h}
    }
