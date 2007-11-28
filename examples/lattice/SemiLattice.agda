
module SemiLattice where

open import Prelude
open import PartialOrder as PO
import Chain

private
 module IsSemiLat
   {A : Set}(po : PartialOrder A)(_⊓_ : A -> A -> A) where
  private open module PO = PartialOrder po

  record IsSemiLattice : Set where
    field
      ⊓-lbL : forall {x y}   -> (x ⊓ y) ≤ x
      ⊓-lbR : forall {x y}   -> (x ⊓ y) ≤ y
      ⊓-glb : forall {x y z} -> z ≤ x -> z ≤ y -> z ≤ (x ⊓ y)

open IsSemiLat public

record SemiLattice (A : Set) : Set1 where
  field
    po  : PartialOrder A
    _⊓_ : A -> A -> A
    prf : IsSemiLattice po _⊓_

module SemiLat {A : Set}(L : SemiLattice A) where

  private module SL   = SemiLattice L
  private module SLPO = POrder SL.po
  private module IsSL = IsSemiLattice SL.po SL._⊓_ SL.prf

  open SLPO public
  open SL   public hiding (prf)
  open IsSL public

  private open module C≤ = Chain _≤_ (\x -> ≤-refl) (\x y z -> ≤-trans)
                      renaming (_===_ to _-≤-_; chain>_ to trans>_)

  ⊓-commute : forall {x y} -> (x ⊓ y) == (y ⊓ x)
  ⊓-commute = ≤-antisym lem lem
    where
      lem : forall {x y} -> (x ⊓ y) ≤ (y ⊓ x)
      lem = ⊓-glb ⊓-lbR ⊓-lbL

  ⊓-assoc : forall {x y z} -> (x ⊓ (y ⊓ z)) == ((x ⊓ y) ⊓ z)
  ⊓-assoc = ≤-antisym lem₁ lem₂
    where
      lem₁ : forall {x y z} -> (x ⊓ (y ⊓ z)) ≤ ((x ⊓ y) ⊓ z)
      lem₁ = ⊓-glb (⊓-glb ⊓-lbL (≤-trans ⊓-lbR ⊓-lbL))
                   (≤-trans ⊓-lbR ⊓-lbR)

      lem₂ : forall {x y z} ->  ((x ⊓ y) ⊓ z) ≤ (x ⊓ (y ⊓ z))
      lem₂ = ⊓-glb (≤-trans ⊓-lbL ⊓-lbL)
                   (⊓-glb (≤-trans ⊓-lbL ⊓-lbR) ⊓-lbR)

  ⊓-idem : forall {x} -> (x ⊓ x) == x
  ⊓-idem = ≤-antisym ⊓-lbL (⊓-glb ≤-refl ≤-refl)

  ≤⊓-L : forall {x y} -> (x ≤ y) ⇐⇒ ((x ⊓ y) == x)
  ≤⊓-L = (fwd , bwd)
    where
      fwd = \x≤y -> ≤-antisym ⊓-lbL (⊓-glb ≤-refl x≤y)
      bwd = \x⊓y=x -> ≤-trans (==≤-R x⊓y=x) ⊓-lbR

  ≤⊓-R : forall {x y} -> (y ≤ x) ⇐⇒ ((x ⊓ y) == y)
  ≤⊓-R {x}{y} = (fwd , bwd)
    where
      lem : (y ≤ x) ⇐⇒ ((y ⊓ x) == y)
      lem = ≤⊓-L

      fwd = \y≤x -> ==-trans ⊓-commute (fst lem y≤x)
      bwd = \x⊓y=y -> snd lem (==-trans ⊓-commute x⊓y=y)

  ⊓-monotone-R : forall {a} -> Monotone (\x -> a ⊓ x)
  ⊓-monotone-R x≤y = ⊓-glb ⊓-lbL (≤-trans ⊓-lbR x≤y)

  ⊓-monotone-L : forall {a} -> Monotone (\x -> x ⊓ a)
  ⊓-monotone-L {a}{x}{y} x≤y = 
    trans> x ⊓ a
       -≤- a ⊓ x  by ==≤-L ⊓-commute
       -≤- a ⊓ y  by ⊓-monotone-R x≤y
       -≤- y ⊓ a  by ==≤-L ⊓-commute

  ≤⊓-compat : forall {w x y z} -> w ≤ y -> x ≤ z -> (w ⊓ x) ≤ (y ⊓ z)
  ≤⊓-compat {w}{x}{y}{z} w≤y x≤z =
    trans> w ⊓ x
       -≤- w ⊓ z  by ⊓-monotone-R x≤z
       -≤- y ⊓ z  by ⊓-monotone-L w≤y

  ⊓-cong : forall {w x y z} -> w == y -> x == z -> (w ⊓ x) == (y ⊓ z)
  ⊓-cong wy xz = ≤-antisym (≤⊓-compat (==≤-L wy) (==≤-L xz))
                           (≤⊓-compat (==≤-R wy) (==≤-R xz))

  ⊓-cong-L : forall {x y z} -> x == y -> (x ⊓ z) == (y ⊓ z)
  ⊓-cong-L xy = ⊓-cong xy ==-refl 

  ⊓-cong-R : forall {x y z} -> x == y -> (z ⊓ x) == (z ⊓ y)
  ⊓-cong-R xy = ⊓-cong ==-refl xy
