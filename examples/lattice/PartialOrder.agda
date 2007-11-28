
module PartialOrder where

open import Prelude

record PartialOrder (A : Set) : Set1 where
  field
    _==_    : A -> A -> Set
    _≤_     : A -> A -> Set
    ==-def  : forall {x y} -> (x == y) ⇐⇒ (x ≤ y) ∧ (y ≤ x)
    ≤-refl  : forall {x} -> x ≤ x
    ≤-trans : forall {x y z} -> x ≤ y -> y ≤ z -> x ≤ z

module POrder {A : Set}(ord : PartialOrder A) where

  private module POrd = PartialOrder ord
  open POrd public

  infix 60 _≤_ _==_

  Monotone : (A -> A) -> Set
  Monotone f = forall {x y} -> x ≤ y -> f x ≤ f y
  
  Antitone : (A -> A) -> Set
  Antitone f = forall {x y} -> x ≤ y -> f y ≤ f x

  ≤-antisym : forall {x y} -> x ≤ y -> y ≤ x -> x == y
  ≤-antisym p q = snd ==-def (p , q)

  ==≤-L : forall {x y} -> x == y -> x ≤ y
  ==≤-L x=y = fst (fst ==-def x=y)

  ==≤-R : forall {x y} -> x == y -> y ≤ x
  ==≤-R x=y = snd (fst ==-def x=y)

  ==-refl : forall {x} -> x == x
  ==-refl = ≤-antisym ≤-refl ≤-refl

  ==-sym : forall {x y} -> x == y -> y == x
  ==-sym xy = snd ==-def (swap (fst ==-def xy))

  ==-trans : forall {x y z} -> x == y -> y == z -> x == z
  ==-trans xy yz = ≤-antisym
                           (≤-trans x≤y y≤z)
                           (≤-trans z≤y y≤x)
    where
      x≤y = ==≤-L xy
      y≤z = ==≤-L yz
      y≤x = ==≤-R xy
      z≤y = ==≤-R yz

  Dual : PartialOrder A
  Dual = record
    { _==_    = _==_
    ; _≤_     = \x y -> y ≤ x
    ; ==-def  = (swap ∘ fst ==-def , snd ==-def ∘ swap)
    ; ≤-refl  = ≤-refl
    ; ≤-trans = \yx zy -> ≤-trans zy yx
    }
