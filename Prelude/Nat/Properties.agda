------------------------------------------------------------------------
-- A bunch of arithmetical properties
------------------------------------------------------------------------

module Prelude.Nat.Properties where

open import Prelude.Nat
open import Prelude.Logic
open import Prelude.Function
import Prelude.Algebra
private
  open module A = Prelude.Algebra ℕ-setoid
open import Prelude.Algebraoid
open import Prelude.BinaryRelation.PropositionalEquality
open import Prelude.Product
open Π

import Prelude.PreorderProof
private
  open module PP = Prelude.PreorderProof ℕ-preSetoid

abstract

  ℕ-+-assoc : Associative _+_
  ℕ-+-assoc zero    _ _ = byDef
  ℕ-+-assoc (suc m) n o = ≡-cong suc $ ℕ-+-assoc m n o

  m+1+n≡1+m+n : forall m n -> m + suc n ≡ suc (m + n)
  m+1+n≡1+m+n zero    n = byDef
  m+1+n≡1+m+n (suc m) n = ≡-cong suc (m+1+n≡1+m+n m n)

  m*1+n≡m+mn : forall m n -> m * suc n ≡ m + m * n
  m*1+n≡m+mn zero    n = byDef
  m*1+n≡m+mn (suc m) n =
      suc m * suc n
    ≃⟨ byDef ⟩
      m * suc n + suc n
    ≃⟨ m+1+n≡1+m+n (m * suc n) n ⟩
      suc (m * suc n + n)
    ≃⟨ ≡-cong (\x -> suc (x + n)) (m*1+n≡m+mn m n) ⟩
      suc (m +  m * n + n)
    ≃⟨ ≡-cong suc (≡-sym (ℕ-+-assoc m (m * n) n)) ⟩
      suc (m + (m * n + n))
    ≃⟨ byDef ⟩
      suc m + suc m * n
    ∎

  ℕ-+-identity : Identity 0 _+_
  ℕ-+-identity = (\_ -> byDef) , n+0≡n
    where
    n+0≡n : RightIdentity 0 _+_
    n+0≡n zero    = byDef
    n+0≡n (suc n) = ≡-cong suc $ n+0≡n n

  ℕ-zero : Zero 0 _*_
  ℕ-zero = (\_ -> byDef) , n*0≡0
    where
    n*0≡0 : RightZero 0 _*_
    n*0≡0 zero    = byDef
    n*0≡0 (suc n) =
        suc n * 0
      ≃⟨ byDef ⟩
        n * 0 + 0
      ≃⟨ proj₂ ℕ-+-identity _ ⟩
        n * 0
      ≃⟨ n*0≡0 n ⟩
        0
      ∎

  ℕ-+-comm : Commutative _+_
  ℕ-+-comm zero    n = ≡-sym $ proj₂ ℕ-+-identity n
  ℕ-+-comm (suc m) n =
      suc m + n
    ≃⟨ byDef ⟩
      suc (m + n)
    ≃⟨ ≡-cong suc (ℕ-+-comm m n) ⟩
      suc (n + m)
    ≃⟨ ≡-sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ∎

  ℕ-*-comm : Commutative _*_
  ℕ-*-comm zero    n = ≡-sym $ proj₂ ℕ-zero n
  ℕ-*-comm (suc m) n =
      suc m * n
    ≃⟨ byDef ⟩
      m * n + n
    ≃⟨ ≡-cong (\x -> x + n) (ℕ-*-comm m n) ⟩
      n * m + n
    ≃⟨ ℕ-+-comm (n * m) n ⟩
      n + n * m
    ≃⟨ ≡-sym (m*1+n≡m+mn n m) ⟩
      n * suc m
    ∎

  m*1+n≡m+m*n : forall m n -> m * suc n ≡ m + m * n
  m*1+n≡m+m*n m n =
      m * suc n
    ≃⟨ ℕ-*-comm m (suc n) ⟩
      suc n * m
    ≃⟨ byDef ⟩
      n * m + m
    ≃⟨ ≡-cong (\x -> x + m) (ℕ-*-comm n m) ⟩
      m * n + m
    ≃⟨ ℕ-+-comm (m * n) m ⟩
      m + m * n
    ∎

  ℕ-*-identity : Identity 1 _*_
  ℕ-*-identity = (\_ -> byDef) , n*1≡n
    where
    n*1≡n : RightIdentity 1 _*_
    n*1≡n n =
        n * 1
      ≃⟨ ℕ-*-comm n 1 ⟩
        1 * n
      ≃⟨ byDef ⟩
        n
      ∎

  ℕ-distrib : _*_ DistributesOver _+_
  ℕ-distrib = distˡ , distʳ
    where
    distˡ : _*_ DistributesOverˡ _+_
    distˡ zero    n o = byDef
    distˡ (suc m) n o =
      suc m * (n + o)
                                 ≃⟨ byDef ⟩
      m * (n + o) + (n + o)
                                 ≃⟨ ≡-cong (\x -> x + (n + o)) (distˡ m n o) ⟩
      (m * n + m * o) + (n + o)
                                 ≃⟨ ≡-sym $ ℕ-+-assoc (m * n) (m * o) (n + o) ⟩
      m * n + (m * o + (n + o))
                                 ≃⟨ ≡-cong (\x -> (m * n) + x) $ ℕ-+-assoc (m * o) n o ⟩
      m * n + ((m * o + n) + o)
                                 ≃⟨ ≡-cong (\x -> (m * n) + (x + o)) $ ℕ-+-comm (m * o) n ⟩
      m * n + ((n + m * o) + o)
                                 ≃⟨ ≡-cong (\x -> (m * n) + x) $ ≡-sym $ ℕ-+-assoc n (m * o) o ⟩
      m * n + (n + (m * o + o))
                                 ≃⟨ ℕ-+-assoc (m * n) n (m * o + o) ⟩
      (m * n + n) + (m * o + o)
                                 ≃⟨ byDef ⟩
      suc m * n + suc m * o
                                 ∎

    distʳ : _*_ DistributesOverʳ _+_
    distʳ m n o =
       (n + o) * m
                      ≃⟨ ℕ-*-comm (n + o) m ⟩
       m * (n + o)
                      ≃⟨ distˡ m n o ⟩
       m * n + m * o
                      ≃⟨ ≡-cong₂ _+_ (ℕ-*-comm m n) (ℕ-*-comm m o) ⟩
       n * m + o * m
                      ∎

  ℕ-*-assoc : Associative _*_
  ℕ-*-assoc zero    n o = byDef
  ℕ-*-assoc (suc m) n o =
    suc m * (n * o)
                         ≃⟨ byDef ⟩
    m * (n * o) + n * o
                         ≃⟨ ≡-cong (\x -> x + n * o) $ ℕ-*-assoc m n o ⟩
    (m * n) * o + n * o
                         ≃⟨ ≡-sym $ proj₂ ℕ-distrib o (m * n) n ⟩
    (m * n + n) * o
                         ≃⟨ byDef ⟩
    (suc m * n) * o
                         ∎

  ℕ-semiring : Semiring _+_ _*_ 0 1
  ℕ-semiring = record
    { +-monoid = record
      { monoid = record
        { semigroup = record
          { assoc    = ℕ-+-assoc
          ; •-pres-≈ = ≡-cong₂ _+_
          }
        ; identity = ℕ-+-identity
        }
      ; comm = ℕ-+-comm
      }
    ; *-monoid = record
      { semigroup = record
        { assoc    = ℕ-*-assoc
        ; •-pres-≈ = ≡-cong₂ _*_
        }
      ; identity = ℕ-*-identity
      }
    ; distrib = ℕ-distrib
    ; zero = ℕ-zero
    }

ℕ-semiringoid : Semiringoid
ℕ-semiringoid = record
  { setoid   = ℕ-setoid
  ; _+_      = _+_
  ; _*_      = _*_
  ; 0#       = 0
  ; 1#       = 1
  ; semiring = ℕ-semiring
  }

abstract

  0∸n≡0 : LeftZero zero _∸_
  0∸n≡0 zero    = byDef
  0∸n≡0 (suc _) = byDef

  ℕ-∸-+-assoc : forall m n o -> (m ∸ n) ∸ o ≡ m ∸ (n + o)
  ℕ-∸-+-assoc m       n       zero    = ≡-cong (_∸_ m) (≡-sym $ proj₂ ℕ-+-identity n)
  ℕ-∸-+-assoc zero    zero    (suc o) = byDef
  ℕ-∸-+-assoc zero    (suc n) (suc o) = byDef
  ℕ-∸-+-assoc (suc m) zero    (suc o) = byDef
  ℕ-∸-+-assoc (suc m) (suc n) (suc o) = ℕ-∸-+-assoc m n (suc o)

abstract

  -- Can we make use of duality in some nice way here?

  ℕ-⊔-assoc : Associative _⊔_
  ℕ-⊔-assoc zero    _       _       = byDef
  ℕ-⊔-assoc (suc m) zero    o       = byDef
  ℕ-⊔-assoc (suc m) (suc n) zero    = byDef
  ℕ-⊔-assoc (suc m) (suc n) (suc o) = ≡-cong suc $ ℕ-⊔-assoc m n o

  ℕ-⊓-assoc : Associative _⊓_
  ℕ-⊓-assoc zero    _       _       = byDef
  ℕ-⊓-assoc (suc m) zero    o       = byDef
  ℕ-⊓-assoc (suc m) (suc n) zero    = byDef
  ℕ-⊓-assoc (suc m) (suc n) (suc o) = ≡-cong suc $ ℕ-⊓-assoc m n o

  ℕ-⊔-identity : Identity 0 _⊔_
  ℕ-⊔-identity = (\_ -> byDef) , n⊔0≡n
    where
    n⊔0≡n : RightIdentity 0 _⊔_
    n⊔0≡n zero    = byDef
    n⊔0≡n (suc n) = byDef

  ℕ-⊓-zero : Zero 0 _⊓_
  ℕ-⊓-zero = (\_ -> byDef) , n⊓0≡0
    where
    n⊓0≡0 : RightZero 0 _⊓_
    n⊓0≡0 zero    = byDef
    n⊓0≡0 (suc n) = byDef

  ℕ-⊔-comm : Commutative _⊔_
  ℕ-⊔-comm zero    n       = ≡-sym $ proj₂ ℕ-⊔-identity n
  ℕ-⊔-comm (suc m) zero    = byDef
  ℕ-⊔-comm (suc m) (suc n) =
      suc m ⊔ suc n
    ≃⟨ byDef ⟩
      suc (m ⊔ n)
    ≃⟨ ≡-cong suc (ℕ-⊔-comm m n) ⟩
      suc (n ⊔ m)
    ≃⟨ byDef ⟩
      suc n ⊔ suc m
    ∎

  ℕ-⊓-comm : Commutative _⊓_
  ℕ-⊓-comm zero    n       = ≡-sym $ proj₂ ℕ-⊓-zero n
  ℕ-⊓-comm (suc m) zero    = byDef
  ℕ-⊓-comm (suc m) (suc n) =
      suc m ⊓ suc n
    ≃⟨ byDef ⟩
      suc (m ⊓ n)
    ≃⟨ ≡-cong suc (ℕ-⊓-comm m n) ⟩
      suc (n ⊓ m)
    ≃⟨ byDef ⟩
      suc n ⊓ suc m
    ∎

  ℕ-distrib-⊓-⊔ : _⊓_ DistributesOver _⊔_
  ℕ-distrib-⊓-⊔ = distˡ , distʳ
    where
    distˡ : _⊓_ DistributesOverˡ _⊔_
    distˡ zero    n       o       = byDef
    distˡ (suc m) zero    o       = byDef
    distˡ (suc m) (suc n) zero    = byDef
    distˡ (suc m) (suc n) (suc o) = ≡-cong suc $ distˡ m n o

    distʳ : _⊓_ DistributesOverʳ _⊔_
    distʳ m n o =
       (n ⊔ o) ⊓ m
                      ≃⟨ ℕ-⊓-comm (n ⊔ o) m ⟩
       m ⊓ (n ⊔ o)
                      ≃⟨ distˡ m n o ⟩
       m ⊓ n ⊔ m ⊓ o
                      ≃⟨ ≡-cong₂ _⊔_ (ℕ-⊓-comm m n) (ℕ-⊓-comm m o) ⟩
       n ⊓ m ⊔ o ⊓ m
                      ∎

  ℕ-absorptive-⊔-⊓ : Absorptive _⊔_ _⊓_
  ℕ-absorptive-⊔-⊓ = abs-⊔-⊓ , abs-⊓-⊔
    where
    abs-⊔-⊓ : _⊔_ Absorbs _⊓_
    abs-⊔-⊓ zero    n       = byDef
    abs-⊔-⊓ (suc m) zero    = byDef
    abs-⊔-⊓ (suc m) (suc n) = ≡-cong suc $ abs-⊔-⊓ m n

    abs-⊓-⊔ : _⊓_ Absorbs _⊔_
    abs-⊓-⊔ zero    n       = byDef
    abs-⊓-⊔ (suc m) (suc n) = ≡-cong suc $ abs-⊓-⊔ m n
    abs-⊓-⊔ (suc m) zero    = ≡-cong suc $
      m ⊓ m
                   ≃⟨ ≡-cong (_⊓_ m) $ ≡-sym $ proj₂ ℕ-⊔-identity m ⟩
      m ⊓ (m ⊔ 0)
                   ≃⟨ abs-⊓-⊔ m zero ⟩
      m
                   ∎

  ℕ-distrib-⊔-⊓ : _⊔_ DistributesOver _⊓_
  ℕ-distrib-⊔-⊓ = distˡ , distʳ
    where
    distˡ : _⊔_ DistributesOverˡ _⊓_
    distˡ zero    n       o       = byDef
    distˡ (suc m) zero    o       = ≡-sym $ proj₂ ℕ-absorptive-⊔-⊓ (suc m) o
    distˡ (suc m) (suc n) (suc o) = ≡-cong suc $ distˡ m n o
    distˡ (suc m) (suc n) zero    = ≡-cong suc $ ≡-sym $
      (m ⊔ n) ⊓ m
                   ≃⟨ ℕ-⊓-comm (m ⊔ n) m ⟩
      m ⊓ (m ⊔ n)
                   ≃⟨ proj₂ ℕ-absorptive-⊔-⊓ m n ⟩
      m
                   ∎

    distʳ : _⊔_ DistributesOverʳ _⊓_
    distʳ m n o =
       (n ⊓ o) ⊔ m
                          ≃⟨ ℕ-⊔-comm (n ⊓ o) m ⟩
       m ⊔ (n ⊓ o)
                          ≃⟨ distˡ m n o ⟩
       (m ⊔ n) ⊓ (m ⊔ o)
                          ≃⟨ ≡-cong₂ _⊓_ (ℕ-⊔-comm m n) (ℕ-⊔-comm m o) ⟩
       (n ⊔ m) ⊓ (o ⊔ m)
                          ∎

  ℕ-lattice : Lattice _⊔_ _⊓_
  ℕ-lattice = record
    { ∨-comm     = ℕ-⊔-comm
    ; ∨-assoc    = ℕ-⊔-assoc
    ; ∨-pres-≈   = ≡-cong₂ _⊔_
    ; ∧-comm     = ℕ-⊓-comm
    ; ∧-assoc    = ℕ-⊓-assoc
    ; ∧-pres-≈   = ≡-cong₂ _⊓_
    ; absorptive = ℕ-absorptive-⊔-⊓
    }

ℕ-latticoid : Latticoid
ℕ-latticoid = record
  { setoid  = ℕ-setoid
  ; _∨_     = _⊔_
  ; _∧_     = _⊓_
  ; lattice = ℕ-lattice
  }
