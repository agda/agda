
module Lattice where

open import Prelude
open import PartialOrder as PO
open import SemiLattice  as SL
import Chain
open POrder using (Dual)

record Lattice (A : Set) : Set1 where
  field
    sl : SemiLattice A
    _⊔_ : A -> A -> A
    prf : IsSemiLattice (Dual (SemiLat.po sl)) _⊔_

module Lat {A : Set}(L : Lattice A) where

  private
    module LL    = Lattice L
    module SLL   = SemiLat LL.sl

  private
    sl' : SemiLattice A
    sl' = record { po = Dual SLL.po; _⊓_ = LL._⊔_; prf = LL.prf }

    module SLL'  = SemiLat sl'
      hiding   ( Monotone
               ; Antitone
               ; _==_; ==-refl; ==-sym; ==-trans
               ; po
               )
      renaming ( _≤_          to _≥_
               ; ≤-refl       to ≥-refl
               ; ≤-trans      to ≥-trans
               ; ≤-antisym    to ≥-antisym
               ; ==≤-L        to ==≥-R
               ; ==≤-R        to ==≥-L
               ; _⊓_          to _⊔_
               ; ⊓-lbL        to ⊔-ubL
               ; ⊓-lbR        to ⊔-ubR
               ; ⊓-glb        to ⊔-lub
               ; ⊓-commute    to ⊔-commute
               ; ⊓-assoc      to ⊔-assoc
               ; ⊓-idem       to ⊔-idem
               ; ≤⊓-L         to ≥⊔-L
               ; ≤⊓-R         to ≥⊔-R
               ; ⊓-monotone-R to ⊔-monotone-R
               ; ⊓-monotone-L to ⊔-monotone-L
               ; ≤⊓-compat    to ≥⊔-compat
               ; ⊓-cong       to ⊔-cong
               ; ⊓-cong-L     to ⊔-cong-L
               ; ⊓-cong-R     to ⊔-cong-R
               )

  open SLL  public
  open SLL' public

  DualLattice : Lattice A
  DualLattice = record { sl = sl'; _⊔_ = _⊓_; prf = SemiLattice.prf LL.sl }

module MeetJoin {A : Set}(L : Lattice A) where 

  private module L = Lat L
  open L

  open module C== = Chain _==_ (\x -> ==-refl) (\x y z -> ==-trans)

  -- Experiment with very explicit proof
  ⊓⊔-absorb-LL = \{x y} ->
    (x ⊓ (x ⊔ y)) == x  from
      ≤-antisym
        ((x ⊓ (x ⊔ y)) ≤ x from ⊓-lbL)
        (x ≤ (x ⊓ (x ⊔ y)) from
          ⊓-glb (x ≤ x       from ≤-refl)
                (x ≤ (x ⊔ y) from ⊔-ubL)
        )

  ⊓⊔-eq : forall {x y} -> (x ⊓ y) == (x ⊔ y) -> x == y
  ⊓⊔-eq {x}{y} p =
    chain> x
       === x ⊓ (x ⊔ y) by ==-sym ⊓⊔-absorb-LL
       === x ⊓ (x ⊓ y) by ==-sym (⊓-cong-R p)
       === (x ⊓ x) ⊓ y by {!!} -- ⊓-assoc
       === x ⊓ y       by ⊓-cong-L ⊓-idem
       === y ⊓ x       by ⊓-commute
       === (y ⊓ y) ⊓ x by ⊓-cong-L (==-sym ⊓-idem)
       === y ⊓ (y ⊓ x) by ==-sym ⊓-assoc
       === y ⊓ (x ⊓ y) by ⊓-cong-R ⊓-commute
       === y ⊓ (x ⊔ y) by {! !} -- ⊓-cong-R p
       === y ⊓ (y ⊔ x) by ⊓-cong-R ⊔-commute
       === y           by ⊓⊔-absorb-LL

module JoinMeet {A : Set}(L : Lattice A) =
  MeetJoin (Lat.DualLattice L)
  hiding (⊓⊔-eq)
  renaming (⊓⊔-absorb-LL to ⊔⊓-absorb-LL)
