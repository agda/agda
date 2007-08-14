------------------------------------------------------------------------
-- A bunch of properties
------------------------------------------------------------------------

module Data.Bool.Properties where

open import Data.Bool
open import Data.Fin
open import Data.Vec
open import Logic
open import Data.Function
import Algebra
import Algebra.Props.CommutativeSemiring as CSProp
import Algebra.Props.CommutativeRing     as CRProp
private
  open module A = Algebra Bool-setoid
open import Algebra.Packaged
open import Relation.Binary.PropositionalEquality
open import Data.Product
import Algebra.RingSolver.Simple as Solver

import Relation.Binary.EqReasoning
private
  open module PP = Relation.Binary.EqReasoning Bool-preSetoid

------------------------------------------------------------------------
-- Duality

-- Can we take advantage of duality in some (nice) way?

------------------------------------------------------------------------
-- (Bool, ∨, ∧, false, true) forms a commutative semiring

abstract
 private

  ∨-assoc : Associative _∨_
  ∨-assoc true  y z = byDef
  ∨-assoc false y z = byDef

  ∧-assoc : Associative _∧_
  ∧-assoc true  y z = byDef
  ∧-assoc false y z = byDef

  ∨-comm : Commutative _∨_
  ∨-comm true  true  = byDef
  ∨-comm true  false = byDef
  ∨-comm false true  = byDef
  ∨-comm false false = byDef

  ∧-comm : Commutative _∧_
  ∧-comm true  true  = byDef
  ∧-comm true  false = byDef
  ∧-comm false true  = byDef
  ∧-comm false false = byDef

  ∨-identity : Identity false _∨_
  ∨-identity = (\_ -> byDef) , (\x -> ∨-comm x false)

  ∧-identity : Identity true _∧_
  ∧-identity = (\_ -> byDef) , (\x -> ∧-comm x true)

  zero-∧ : Zero false _∧_
  zero-∧ = (\_ -> byDef) , (\x -> ∧-comm x false)

  distrib-∧-∨ : _∧_ DistributesOver _∨_
  distrib-∧-∨ = distˡ , distʳ
    where
    distˡ : _∧_ DistributesOverˡ _∨_
    distˡ true  y z = byDef
    distˡ false y z = byDef

    distʳ : _∧_ DistributesOverʳ _∨_
    distʳ x y z =
                      begin
       (y ∨ z) ∧ x
                      ∼⟨ ∧-comm (y ∨ z) x ⟩
       x ∧ (y ∨ z)
                      ∼⟨ distˡ x y z ⟩
       x ∧ y ∨ x ∧ z
                      ∼⟨ ≡-cong₂ _∨_ (∧-comm x y) (∧-comm x z) ⟩
       y ∧ x ∨ z ∧ x
                      ∎

abstract

  Bool-semiring-∨-∧ : Semiring _∨_ _∧_ false true
  Bool-semiring-∨-∧ = record
    { +-monoid = record
      { monoid = record
        { semigroup = record
          { assoc    = ∨-assoc
          ; •-pres-≈ = ≡-cong₂ _∨_
          }
        ; identity = ∨-identity
        }
      ; comm = ∨-comm
      }
    ; *-monoid = record
      { semigroup = record
        { assoc    = ∧-assoc
        ; •-pres-≈ = ≡-cong₂ _∧_
        }
      ; identity = ∧-identity
      }
    ; distrib = distrib-∧-∨
    ; zero = zero-∧
    }

  Bool-commSemiring-∨-∧ : CommutativeSemiring _∨_ _∧_ false true
  Bool-commSemiring-∨-∧ = record
    { semiring = Bool-semiring-∨-∧
    ; *-comm   = ∧-comm
    }

Bool-commSemiringoid-∨-∧ : CommutativeSemiringoid
Bool-commSemiringoid-∨-∧ = record
  { setoid       = Bool-setoid
  ; _+_          = _∨_
  ; _*_          = _∧_
  ; 0#           = false
  ; 1#           = true
  ; commSemiring = Bool-commSemiring-∨-∧
  }

module Bool-ringSolver =
  Solver (CSProp.almostCommRingoid Bool-commSemiringoid-∨-∧)

------------------------------------------------------------------------
-- (Bool, ∧, ∨, true, false) forms a commutative semiring

abstract
 private

  zero-∨ : Zero true _∨_
  zero-∨ = (\_ -> byDef) , (\x -> ∨-comm x true)

  distrib-∨-∧ : _∨_ DistributesOver _∧_
  distrib-∨-∧ = distˡ , distʳ
    where
    distˡ : _∨_ DistributesOverˡ _∧_
    distˡ true  y z = byDef
    distˡ false y z = byDef

    distʳ : _∨_ DistributesOverʳ _∧_
    distʳ x y z =
                          begin
       (y ∧ z) ∨ x
                          ∼⟨ ∨-comm (y ∧ z) x ⟩
       x ∨ (y ∧ z)
                          ∼⟨ distˡ x y z ⟩
       (x ∨ y) ∧ (x ∨ z)
                          ∼⟨ ≡-cong₂ _∧_ (∨-comm x y) (∨-comm x z) ⟩
       (y ∨ x) ∧ (z ∨ x)
                          ∎

abstract

  Bool-semiring-∧-∨ : Semiring _∧_ _∨_ true false
  Bool-semiring-∧-∨ = record
    { +-monoid = record
      { monoid = record
        { semigroup = record
          { assoc    = ∧-assoc
          ; •-pres-≈ = ≡-cong₂ _∧_
          }
        ; identity = ∧-identity
        }
      ; comm = ∧-comm
      }
    ; *-monoid = record
      { semigroup = record
        { assoc    = ∨-assoc
        ; •-pres-≈ = ≡-cong₂ _∨_
        }
      ; identity = ∨-identity
      }
    ; distrib = distrib-∨-∧
    ; zero = zero-∨
    }

  Bool-commSemiring-∧-∨ : CommutativeSemiring _∧_ _∨_ true false
  Bool-commSemiring-∧-∨ = record
    { semiring = Bool-semiring-∧-∨
    ; *-comm   = ∨-comm
    }

Bool-commSemiringoid-∧-∨ : CommutativeSemiringoid
Bool-commSemiringoid-∧-∨ = record
  { setoid       = Bool-setoid
  ; _+_          = _∧_
  ; _*_          = _∨_
  ; 0#           = true
  ; 1#           = false
  ; commSemiring = Bool-commSemiring-∧-∨
  }

------------------------------------------------------------------------
-- (Bool, ∨, ∧) is a distributive lattice

abstract
 private

  absorptive : Absorptive _∨_ _∧_
  absorptive = abs-∨-∧ , abs-∧-∨
    where
    abs-∨-∧ : _∨_ Absorbs _∧_
    abs-∨-∧ true  y = byDef
    abs-∨-∧ false y = byDef

    abs-∧-∨ : _∧_ Absorbs _∨_
    abs-∧-∨ true  y = byDef
    abs-∧-∨ false y = byDef

abstract

  Bool-lattice : Lattice _∨_ _∧_
  Bool-lattice = record
    { ∨-comm     = ∨-comm
    ; ∨-assoc    = ∨-assoc
    ; ∨-pres-≈   = ≡-cong₂ _∨_
    ; ∧-comm     = ∧-comm
    ; ∧-assoc    = ∧-assoc
    ; ∧-pres-≈   = ≡-cong₂ _∧_
    ; absorptive = absorptive
    }

  Bool-distLattice : DistributiveLattice _∨_ _∧_
  Bool-distLattice = record
    { lattice      = Bool-lattice
    ; ∨-∧-distribˡ = proj₁ distrib-∨-∧
    }

------------------------------------------------------------------------
-- (Bool, ∨, ∧, not, true, false) is a boolean algebra

abstract
 private
  not-∧-inverse : Inverse false not _∧_
  not-∧-inverse =
    ¬x∧x≡⊥ , (\x -> ∧-comm x (not x) ⟨ ≡-trans ⟩ ¬x∧x≡⊥ x)
    where
    ¬x∧x≡⊥ : LeftInverse false not _∧_
    ¬x∧x≡⊥ false = byDef
    ¬x∧x≡⊥ true  = byDef

  not-∨-inverse : Inverse true not _∨_
  not-∨-inverse =
    ¬x∨x≡⊤ , (\x -> ∨-comm x (not x) ⟨ ≡-trans ⟩ ¬x∨x≡⊤ x)
    where
    ¬x∨x≡⊤ : LeftInverse true not _∨_
    ¬x∨x≡⊤ false = byDef
    ¬x∨x≡⊤ true  = byDef

abstract

  Bool-booleanAlgebra : BooleanAlgebra _∨_ _∧_ not true false
  Bool-booleanAlgebra = record
    { distLattice   = Bool-distLattice
    ; ∨-complementʳ = proj₂ not-∨-inverse
    ; ∧-complementʳ = proj₂ not-∧-inverse
    ; ¬-pres-≈      = ≡-cong not
    }

Bool-booleanAlgebraoid : BooleanAlgebraoid
Bool-booleanAlgebraoid = record
  { setoid         = Bool-setoid
  ; _∨_            = _∨_
  ; _∧_            = _∧_
  ; ¬_             = not
  ; ⊤              = true
  ; ⊥              = false
  ; booleanAlgebra = Bool-booleanAlgebra
  }

------------------------------------------------------------------------
-- (Bool, xor, ∧, id, false, true) forms a commutative ring

abstract
 private

  xor-is-ok : forall x y -> x xor y ≡ (x ∨ y) ∧ not (x ∧ y)
  xor-is-ok true  y = byDef
  xor-is-ok false y = ≡-sym $ proj₂ ∧-identity _

Bool-commRingoid-xor-∧ : CommutativeRingoid
Bool-commRingoid-xor-∧ = record
  { bare = record
    { setoid = Bool-setoid
    ; _+_    = _xor_
    ; _*_    = _∧_
    ; -_     = id
    ; 0#     = false
    ; 1#     = true
    }
  ; commRing = R.commRing
  }
  where
  import Algebra.Props.BooleanAlgebra
  module P = Algebra.Props.BooleanAlgebra
               Bool-booleanAlgebraoid
  module R = P.XorRing _xor_ xor-is-ok

module Bool-xor-ringSolver =
  Solver (CRProp.almostCommRingoid Bool-commRingoid-xor-∧)

------------------------------------------------------------------------
-- Miscellaneous other properties

abstract

  Bool-not-involutive : Involutive not
  Bool-not-involutive true  = byDef
  Bool-not-involutive false = byDef
