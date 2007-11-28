
module Setoid where

open import Logic.Base

record Setoid : Set1 where
  field
    A     : Set
    _==_  : A -> A -> Prop
    refl  : {x : A} -> x == x
    sym   : {x y : A} -> x == y -> y == x
    trans : {x y z : A} -> x == y -> y == z -> x == z




module Set-Ar where

  !_! : (S : Setoid) -> Set
  ! S ! = Setoid.A S


  record SetoidArrow (S₁ S₂ : Setoid) : Set where
    field
      map  : ! S₁ ! -> ! S₂ !
      stab : {x y : Setoid.A S₁} -> Setoid._==_ S₁ x y -> Setoid._==_ S₂ (map x) (map y)

  _∘_ : {S₁ S₂ S₃ : Setoid} -> SetoidArrow S₂ S₃ -> SetoidArrow S₁ S₂ -> SetoidArrow S₁ S₃
  _∘_ {S₁} F₁ F₂ = record 
    { map  = \x -> SetoidArrow.map F₁ (SetoidArrow.map F₂ x)
    ; stab = \{x y : ! S₁ !}(p : Setoid._==_ S₁ x y) -> SetoidArrow.stab F₁ (SetoidArrow.stab F₂ p)
    }

  id : {S : Setoid} -> SetoidArrow S S
  id = record
    { map  = \x -> x
    ; stab = \p -> p
    }

  _==→_ : {S₁ S₂ : Setoid} -> SetoidArrow S₁ S₂ -> SetoidArrow S₁ S₂ -> Set
  _==→_ {_} {S₂} F₁ F₂ = (forall x -> Setoid._==_ S₂ (SetoidArrow.map F₁ x) (SetoidArrow.map F₂ x)) -> True


module Set-Fam where
  
  open Set-Ar

  record SetoidFam (S : Setoid) : Set1 where
    field
      index     : ! S ! -> Setoid
      reindex   : {x x' : ! S !} -> Setoid._==_ S x x' -> SetoidArrow (index x) (index x')
      id-coh    : {x : ! S !} -> (reindex (Setoid.refl S)) ==→ id {index x}
      sym-coh-l : {x y : ! S !}(p : Setoid._==_ S x y) -> ((reindex (Setoid.sym S p)) ∘ (reindex p)) ==→ id
      sym-coh-r : {x y : ! S !}(p : Setoid._==_ S x y) -> ((reindex p) ∘ (reindex (Setoid.sym S p))) ==→ id
      trans-coh : {x y z : ! S !}(p : Setoid._==_ S x y)(p' : Setoid._==_ S y z) -> 
                  (reindex (Setoid.trans S p p')) ==→ ((reindex p') ∘ (reindex p))


module Set-Fam-Ar where
  
  open Set-Ar
  open Set-Fam 

  record SetoidFamArrow {S₁ S₂ : Setoid}(F₁ : SetoidFam S₁)(F₂ : SetoidFam S₂) : Set where
    field
      indexingmap : SetoidArrow S₁ S₂
      indexmap    : (x : ! S₁ !) -> SetoidArrow (SetoidFam.index F₁ x) 
                    (SetoidFam.index F₂ (SetoidArrow.map indexingmap x))
      reindexmap  : (x x' : ! S₁ !)(p : Setoid._==_ S₁ x' x) ->
                    ((indexmap x) ∘ (SetoidFam.reindex F₁ p)) ==→ 
                    ((SetoidFam.reindex F₂ (SetoidArrow.stab indexingmap p)) ∘ (indexmap x'))
