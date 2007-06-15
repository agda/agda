------------------------------------------------------------------------
-- A bunch of properties
------------------------------------------------------------------------

module Prelude.Bool.Properties where

open import Prelude.Bool
open import Prelude.Logic
open import Prelude.Function
import Prelude.Algebra
private
  open module A = Prelude.Algebra Bool-setoid
open import Prelude.Algebraoid
open import Prelude.BinaryRelation.PropositionalEquality
open import Prelude.Product
open Π

import Prelude.PreorderProof
private
  open module PP = Prelude.PreorderProof Bool-preSetoid

------------------------------------------------------------------------
-- Duality

-- Can we take advantage of duality in some (nice) way?

------------------------------------------------------------------------
-- Various algebraic properties

abstract

  Bool-∨-assoc : Associative _∨_
  Bool-∨-assoc true  y z = byDef
  Bool-∨-assoc false y z = byDef

  Bool-∧-assoc : Associative _∧_
  Bool-∧-assoc true  y z = byDef
  Bool-∧-assoc false y z = byDef

  Bool-∨-comm : Commutative _∨_
  Bool-∨-comm true  true  = byDef
  Bool-∨-comm true  false = byDef
  Bool-∨-comm false true  = byDef
  Bool-∨-comm false false = byDef

  Bool-∧-comm : Commutative _∧_
  Bool-∧-comm true  true  = byDef
  Bool-∧-comm true  false = byDef
  Bool-∧-comm false true  = byDef
  Bool-∧-comm false false = byDef

  Bool-∨-identity : Identity false _∨_
  Bool-∨-identity = (\_ -> byDef) , (\x -> Bool-∨-comm x false)

  Bool-∧-identity : Identity true _∧_
  Bool-∧-identity = (\_ -> byDef) , (\x -> Bool-∧-comm x true)

  Bool-zero-∧ : Zero false _∧_
  Bool-zero-∧ = (\_ -> byDef) , (\x -> Bool-∧-comm x false)

  Bool-zero-∨ : Zero true _∨_
  Bool-zero-∨ = (\_ -> byDef) , (\x -> Bool-∨-comm x true)

  Bool-not-∧-inverse : Inverse false not _∧_
  Bool-not-∧-inverse =
    ¬x∧x≡⊥ , (\x -> Bool-∧-comm x (not x) ⟨ ≡-trans ⟩ ¬x∧x≡⊥ x)
    where
    ¬x∧x≡⊥ : LeftInverse false not _∧_
    ¬x∧x≡⊥ false = byDef
    ¬x∧x≡⊥ true  = byDef

  Bool-not-∨-inverse : Inverse true not _∨_
  Bool-not-∨-inverse =
    ¬x∨x≡⊤ , (\x -> Bool-∨-comm x (not x) ⟨ ≡-trans ⟩ ¬x∨x≡⊤ x)
    where
    ¬x∨x≡⊤ : LeftInverse true not _∨_
    ¬x∨x≡⊤ false = byDef
    ¬x∨x≡⊤ true  = byDef

  Bool-distrib-∧-∨ : _∧_ DistributesOver _∨_
  Bool-distrib-∧-∨ = distˡ , distʳ
    where
    distˡ : _∧_ DistributesOverˡ _∨_
    distˡ true  y z = byDef
    distˡ false y z = byDef

    distʳ : _∧_ DistributesOverʳ _∨_
    distʳ x y z =
       (y ∨ z) ∧ x
                      ≃⟨ Bool-∧-comm (y ∨ z) x ⟩
       x ∧ (y ∨ z)
                      ≃⟨ distˡ x y z ⟩
       x ∧ y ∨ x ∧ z
                      ≃⟨ ≡-cong₂ _∨_ (Bool-∧-comm x y) (Bool-∧-comm x z) ⟩
       y ∧ x ∨ z ∧ x
                      ∎

  Bool-distrib-∨-∧ : _∨_ DistributesOver _∧_
  Bool-distrib-∨-∧ = distˡ , distʳ
    where
    distˡ : _∨_ DistributesOverˡ _∧_
    distˡ true  y z = byDef
    distˡ false y z = byDef

    distʳ : _∨_ DistributesOverʳ _∧_
    distʳ x y z =
       (y ∧ z) ∨ x
                          ≃⟨ Bool-∨-comm (y ∧ z) x ⟩
       x ∨ (y ∧ z)
                          ≃⟨ distˡ x y z ⟩
       (x ∨ y) ∧ (x ∨ z)
                          ≃⟨ ≡-cong₂ _∧_ (Bool-∨-comm x y) (Bool-∨-comm x z) ⟩
       (y ∨ x) ∧ (z ∨ x)
                          ∎

  Bool-semiring-∨-∧ : Semiring _∨_ _∧_ false true
  Bool-semiring-∨-∧ = record
    { +-monoid = record
      { monoid = record
        { semigroup = record
          { assoc    = Bool-∨-assoc
          ; •-pres-≈ = ≡-cong₂ _∨_
          }
        ; identity = Bool-∨-identity
        }
      ; comm = Bool-∨-comm
      }
    ; *-monoid = record
      { semigroup = record
        { assoc    = Bool-∧-assoc
        ; •-pres-≈ = ≡-cong₂ _∧_
        }
      ; identity = Bool-∧-identity
      }
    ; distrib = Bool-distrib-∧-∨
    ; zero = Bool-zero-∧
    }

  Bool-semiring-∧-∨ : Semiring _∧_ _∨_ true false
  Bool-semiring-∧-∨ = record
    { +-monoid = record
      { monoid = record
        { semigroup = record
          { assoc    = Bool-∧-assoc
          ; •-pres-≈ = ≡-cong₂ _∧_
          }
        ; identity = Bool-∧-identity
        }
      ; comm = Bool-∧-comm
      }
    ; *-monoid = record
      { semigroup = record
        { assoc    = Bool-∨-assoc
        ; •-pres-≈ = ≡-cong₂ _∨_
        }
      ; identity = Bool-∨-identity
      }
    ; distrib = Bool-distrib-∨-∧
    ; zero = Bool-zero-∨
    }

  Bool-absorptive : Absorptive _∨_ _∧_
  Bool-absorptive = abs-∨-∧ , abs-∧-∨
    where
    abs-∨-∧ : _∨_ Absorbs _∧_
    abs-∨-∧ true  y = byDef
    abs-∨-∧ false y = byDef

    abs-∧-∨ : _∧_ Absorbs _∨_
    abs-∧-∨ true  y = byDef
    abs-∧-∨ false y = byDef

  Bool-lattice : Lattice _∨_ _∧_
  Bool-lattice = record
    { ∨-comm     = Bool-∨-comm
    ; ∨-assoc    = Bool-∨-assoc
    ; ∨-pres-≈   = ≡-cong₂ _∨_
    ; ∧-comm     = Bool-∧-comm
    ; ∧-assoc    = Bool-∧-assoc
    ; ∧-pres-≈   = ≡-cong₂ _∧_
    ; absorptive = Bool-absorptive
    }

Bool-semiringoid-∨-∧ : Semiringoid
Bool-semiringoid-∨-∧ = record
  { setoid   = Bool-setoid
  ; _+_      = _∨_
  ; _*_      = _∧_
  ; 0#       = false
  ; 1#       = true
  ; semiring = Bool-semiring-∨-∧
  }

Bool-semiringoid-∧-∨ : Semiringoid
Bool-semiringoid-∧-∨ = record
  { setoid   = Bool-setoid
  ; _+_      = _∧_
  ; _*_      = _∨_
  ; 0#       = true
  ; 1#       = false
  ; semiring = Bool-semiring-∧-∨
  }

Bool-latticoid : Latticoid
Bool-latticoid = record
  { setoid  = Bool-setoid
  ; _∨_     = _∨_
  ; _∧_     = _∧_
  ; lattice = Bool-lattice
  }
