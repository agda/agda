------------------------------------------------------------------------
-- A bunch of properties about natural number operations
------------------------------------------------------------------------

module Data.Nat.Properties where

open import Data.Nat
open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; byDef to ≤-refl)
open import Logic
open import Data.Function
open import Algebra
open import Algebra.Structures
import Algebra.FunctionProperties as P; open P ℕ-setoid
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Product

import Relation.Binary.EqReasoning as EqR; open EqR ℕ-setoid

------------------------------------------------------------------------
-- (ℕ, +, *, 0, 1) is a commutative semiring

abstract
 private

  +-assoc : Associative _+_
  +-assoc zero    _ _ = byDef
  +-assoc (suc m) n o = ≡-cong suc $ +-assoc m n o

  +-identity : Identity 0 _+_
  +-identity = (\_ -> byDef) , n+0≡n
    where
    n+0≡n : RightIdentity 0 _+_
    n+0≡n zero    = byDef
    n+0≡n (suc n) = ≡-cong suc $ n+0≡n n

  m+1+n≡1+m+n : forall m n -> m + suc n ≡ suc (m + n)
  m+1+n≡1+m+n zero    n = byDef
  m+1+n≡1+m+n (suc m) n = ≡-cong suc (m+1+n≡1+m+n m n)

  +-comm : Commutative _+_
  +-comm zero    n = ≡-sym $ proj₂ +-identity n
  +-comm (suc m) n =
    begin
      suc m + n
    ≈⟨ byDef ⟩
      suc (m + n)
    ≈⟨ ≡-cong suc (+-comm m n) ⟩
      suc (n + m)
    ≈⟨ ≡-sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ∎

  m*1+n≡m+mn : forall m n -> m * suc n ≡ m + m * n
  m*1+n≡m+mn zero    n = byDef
  m*1+n≡m+mn (suc m) n =
    begin
      suc m * suc n
    ≈⟨ byDef ⟩
      m * suc n + suc n
    ≈⟨ m+1+n≡1+m+n (m * suc n) n ⟩
      suc (m * suc n + n)
    ≈⟨ ≡-cong (\x -> suc (x + n)) (m*1+n≡m+mn m n) ⟩
      suc (m +  m * n + n)
    ≈⟨ ≡-cong suc (≡-sym (+-assoc m (m * n) n)) ⟩
      suc (m + (m * n + n))
    ≈⟨ byDef ⟩
      suc m + suc m * n
    ∎

  *-zero : Zero 0 _*_
  *-zero = (\_ -> byDef) , n*0≡0
    where
    n*0≡0 : RightZero 0 _*_
    n*0≡0 zero    = byDef
    n*0≡0 (suc n) =
      begin
        suc n * 0
      ≈⟨ byDef ⟩
        n * 0 + 0
      ≈⟨ proj₂ +-identity _ ⟩
        n * 0
      ≈⟨ n*0≡0 n ⟩
        0
      ∎

  *-comm : Commutative _*_
  *-comm zero    n = ≡-sym $ proj₂ *-zero n
  *-comm (suc m) n =
    begin
      suc m * n
    ≈⟨ byDef ⟩
      m * n + n
    ≈⟨ ≡-cong (\x -> x + n) (*-comm m n) ⟩
      n * m + n
    ≈⟨ +-comm (n * m) n ⟩
      n + n * m
    ≈⟨ ≡-sym (m*1+n≡m+mn n m) ⟩
      n * suc m
    ∎

  distrib-*-+ : _*_ DistributesOver _+_
  distrib-*-+ = distˡ , distʳ
    where
    distˡ : _*_ DistributesOverˡ _+_
    distˡ zero    n o = byDef
    distˡ (suc m) n o =
                                 begin
      suc m * (n + o)
                                 ≈⟨ byDef ⟩
      m * (n + o) + (n + o)
                                 ≈⟨ ≡-cong (\x -> x + (n + o)) (distˡ m n o) ⟩
      (m * n + m * o) + (n + o)
                                 ≈⟨ ≡-sym $ +-assoc (m * n) (m * o) (n + o) ⟩
      m * n + (m * o + (n + o))
                                 ≈⟨ ≡-cong (\x -> (m * n) + x) $ +-assoc (m * o) n o ⟩
      m * n + ((m * o + n) + o)
                                 ≈⟨ ≡-cong (\x -> (m * n) + (x + o)) $ +-comm (m * o) n ⟩
      m * n + ((n + m * o) + o)
                                 ≈⟨ ≡-cong (\x -> (m * n) + x) $ ≡-sym $ +-assoc n (m * o) o ⟩
      m * n + (n + (m * o + o))
                                 ≈⟨ +-assoc (m * n) n (m * o + o) ⟩
      (m * n + n) + (m * o + o)
                                 ≈⟨ byDef ⟩
      suc m * n + suc m * o
                                 ∎

    distʳ : _*_ DistributesOverʳ _+_
    distʳ m n o =
                      begin
       (n + o) * m
                      ≈⟨ *-comm (n + o) m ⟩
       m * (n + o)
                      ≈⟨ distˡ m n o ⟩
       m * n + m * o
                      ≈⟨ ≡-cong₂ _+_ (*-comm m n) (*-comm m o) ⟩
       n * m + o * m
                      ∎

  *-assoc : Associative _*_
  *-assoc zero    n o = byDef
  *-assoc (suc m) n o =
                         begin
    suc m * (n * o)
                         ≈⟨ byDef ⟩
    m * (n * o) + n * o
                         ≈⟨ ≡-cong (\x -> x + n * o) $ *-assoc m n o ⟩
    (m * n) * o + n * o
                         ≈⟨ ≡-sym $ proj₂ distrib-*-+ o (m * n) n ⟩
    (m * n + n) * o
                         ≈⟨ byDef ⟩
    (suc m * n) * o
                         ∎

  *-identity : Identity 1 _*_
  *-identity = (\_ -> byDef) , n*1≡n
    where
    n*1≡n : RightIdentity 1 _*_
    n*1≡n n =
      begin
        n * 1
      ≈⟨ *-comm n 1 ⟩
        1 * n
      ≈⟨ byDef ⟩
        n
      ∎

abstract

  ℕ-isCommutativeSemiring : IsCommutativeSemiring ℕ-setoid _+_ _*_ 0 1
  ℕ-isCommutativeSemiring = record
    { isSemiring = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { assoc    = +-assoc
            ; •-pres-≈ = ≡-cong₂ _+_
            }
          ; identity = +-identity
          }
        ; comm = +-comm
        }
      ; *-isMonoid = record
        { isSemigroup = record
          { assoc    = *-assoc
          ; •-pres-≈ = ≡-cong₂ _*_
          }
        ; identity = *-identity
        }
      ; distrib = distrib-*-+
      ; zero = *-zero
      }
    ; *-comm = *-comm
    }

ℕ-commutativeSemiring : CommutativeSemiring
ℕ-commutativeSemiring = record
  { setoid                = ℕ-setoid
  ; _+_                   = _+_
  ; _*_                   = _*_
  ; 0#                    = 0
  ; 1#                    = 1
  ; isCommutativeSemiring = ℕ-isCommutativeSemiring
  }

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module ℕ-semiringSolver =
  Solver (ACR.fromCommutativeSemiring ℕ-commutativeSemiring)

------------------------------------------------------------------------
-- (ℕ, ⊔, 0) is a commutative monoid

abstract
 private

  ⊔-identity : Identity 0 _⊔_
  ⊔-identity = (\_ -> byDef) , n⊔0≡n
    where
    n⊔0≡n : RightIdentity 0 _⊔_
    n⊔0≡n zero    = byDef
    n⊔0≡n (suc n) = byDef

  ⊔-comm : Commutative _⊔_
  ⊔-comm zero    n       = ≡-sym $ proj₂ ⊔-identity n
  ⊔-comm (suc m) zero    = byDef
  ⊔-comm (suc m) (suc n) =
    begin
      suc m ⊔ suc n
    ≈⟨ byDef ⟩
      suc (m ⊔ n)
    ≈⟨ ≡-cong suc (⊔-comm m n) ⟩
      suc (n ⊔ m)
    ≈⟨ byDef ⟩
      suc n ⊔ suc m
    ∎

  ⊔-assoc : Associative _⊔_
  ⊔-assoc zero    _       _       = byDef
  ⊔-assoc (suc m) zero    o       = byDef
  ⊔-assoc (suc m) (suc n) zero    = byDef
  ⊔-assoc (suc m) (suc n) (suc o) = ≡-cong suc $ ⊔-assoc m n o

abstract

  ℕ-⊔-0-isCommutativeMonoid : IsCommutativeMonoid ℕ-setoid _⊔_ 0
  ℕ-⊔-0-isCommutativeMonoid = record
    { isMonoid = record
        { isSemigroup = record
            { assoc = ⊔-assoc
            ; •-pres-≈ = ≡-cong₂ _⊔_
            }
        ; identity = ⊔-identity
        }
    ; comm = ⊔-comm
    }

ℕ-⊔-0-commutativeMonoid : CommutativeMonoid
ℕ-⊔-0-commutativeMonoid = record
  { setoid              = ℕ-setoid
  ; _•_                 = _⊔_
  ; ε                   = 0
  ; isCommutativeMonoid = ℕ-⊔-0-isCommutativeMonoid
  }

------------------------------------------------------------------------
-- (ℕ, ⊔, ⊓, 0) is a near-semiring

-- In fact it is something stronger: a semiring without one.

abstract
 private

  ⊓-assoc : Associative _⊓_
  ⊓-assoc zero    _       _       = byDef
  ⊓-assoc (suc m) zero    o       = byDef
  ⊓-assoc (suc m) (suc n) zero    = byDef
  ⊓-assoc (suc m) (suc n) (suc o) = ≡-cong suc $ ⊓-assoc m n o

  ⊓-zero : Zero 0 _⊓_
  ⊓-zero = (\_ -> byDef) , n⊓0≡0
    where
    n⊓0≡0 : RightZero 0 _⊓_
    n⊓0≡0 zero    = byDef
    n⊓0≡0 (suc n) = byDef

  ⊓-comm : Commutative _⊓_
  ⊓-comm zero    n       = ≡-sym $ proj₂ ⊓-zero n
  ⊓-comm (suc m) zero    = byDef
  ⊓-comm (suc m) (suc n) =
    begin
      suc m ⊓ suc n
    ≈⟨ byDef ⟩
      suc (m ⊓ n)
    ≈⟨ ≡-cong suc (⊓-comm m n) ⟩
      suc (n ⊓ m)
    ≈⟨ byDef ⟩
      suc n ⊓ suc m
    ∎

  absorptive-⊓-⊔ : Absorptive _⊓_ _⊔_
  absorptive-⊓-⊔ = abs-⊓-⊔ , abs-⊔-⊓
    where
    abs-⊔-⊓ : _⊔_ Absorbs _⊓_
    abs-⊔-⊓ zero    n       = byDef
    abs-⊔-⊓ (suc m) zero    = byDef
    abs-⊔-⊓ (suc m) (suc n) = ≡-cong suc $ abs-⊔-⊓ m n

    abs-⊓-⊔ : _⊓_ Absorbs _⊔_
    abs-⊓-⊔ zero    n       = byDef
    abs-⊓-⊔ (suc m) (suc n) = ≡-cong suc $ abs-⊓-⊔ m n
    abs-⊓-⊔ (suc m) zero    = ≡-cong suc $
                   begin
      m ⊓ m
                   ≈⟨ ≡-cong (_⊓_ m) $ ≡-sym $ proj₂ ⊔-identity m ⟩
      m ⊓ (m ⊔ 0)
                   ≈⟨ abs-⊓-⊔ m zero ⟩
      m
                   ∎

  distribʳ-⊓-⊔ : _⊓_ DistributesOverʳ _⊔_
  distribʳ-⊓-⊔ (suc m) (suc n) (suc o) = ≡-cong suc $ distribʳ-⊓-⊔ m n o
  distribʳ-⊓-⊔ (suc m) (suc n) zero    = ≡-cong suc $ byDef
  distribʳ-⊓-⊔ (suc m) zero    o       = byDef
  distribʳ-⊓-⊔ zero    n       o       = begin
    (n ⊔ o) ⊓ 0    ≈⟨ ⊓-comm (n ⊔ o) 0 ⟩
    0 ⊓ (n ⊔ o)    ≈⟨ byDef ⟩
    0 ⊓ n ⊔ 0 ⊓ o  ≈⟨ ⊓-comm 0 n ⟨ ≡-cong₂ _⊔_ ⟩ ⊓-comm 0 o ⟩
    n ⊓ 0 ⊔ o ⊓ 0  ∎

abstract

  ℕ-⊔-⊓-0-isNearSemiring : IsNearSemiring ℕ-setoid _⊔_ _⊓_ 0
  ℕ-⊔-⊓-0-isNearSemiring = record
    { +-isMonoid = IsCommutativeMonoid.isMonoid
                     _ ℕ-⊔-0-isCommutativeMonoid
    ; *-isSemigroup = record
        { assoc    = ⊓-assoc
        ; •-pres-≈ = ≡-cong₂ _⊓_
        }
    ; distribʳ = distribʳ-⊓-⊔
    ; zeroˡ    = proj₁ ⊓-zero
    }

ℕ-⊔-⊓-0-nearSemiring : NearSemiring
ℕ-⊔-⊓-0-nearSemiring = record
  { setoid         = ℕ-setoid
  ; _+_            = _⊔_
  ; _*_            = _⊓_
  ; 0#             = 0
  ; isNearSemiring = ℕ-⊔-⊓-0-isNearSemiring
  }

------------------------------------------------------------------------
-- (ℕ, ⊓, ⊔) is a lattice

abstract

  ℕ-isDistributiveLattice : IsDistributiveLattice ℕ-setoid _⊓_ _⊔_
  ℕ-isDistributiveLattice = record
    { isLattice = record
        { ∨-comm     = ⊓-comm
        ; ∨-assoc    = ⊓-assoc
        ; ∨-pres-≈   = ≡-cong₂ _⊓_
        ; ∧-comm     = ⊔-comm
        ; ∧-assoc    = ⊔-assoc
        ; ∧-pres-≈   = ≡-cong₂ _⊔_
        ; absorptive = absorptive-⊓-⊔
        }
    ; ∨-∧-distribʳ = distribʳ-⊓-⊔
    }

ℕ-distributiveLattice : DistributiveLattice
ℕ-distributiveLattice = record
  { setoid                = ℕ-setoid
  ; _∨_                   = _⊓_
  ; _∧_                   = _⊔_
  ; isDistributiveLattice = ℕ-isDistributiveLattice
  }

------------------------------------------------------------------------
-- Miscellaneous other properties

abstract

  0∸n≡0 : LeftZero zero _∸_
  0∸n≡0 zero    = byDef
  0∸n≡0 (suc _) = byDef

  ℕ-∸-+-assoc : forall m n o -> (m ∸ n) ∸ o ≡ m ∸ (n + o)
  ℕ-∸-+-assoc m       n       zero    = ≡-cong (_∸_ m) (≡-sym $ proj₂ +-identity n)
  ℕ-∸-+-assoc zero    zero    (suc o) = byDef
  ℕ-∸-+-assoc zero    (suc n) (suc o) = byDef
  ℕ-∸-+-assoc (suc m) zero    (suc o) = byDef
  ℕ-∸-+-assoc (suc m) (suc n) (suc o) = ℕ-∸-+-assoc m n (suc o)

  m+n∸n≡m : forall m n -> (m + n) ∸ n ≡ m
  m+n∸n≡m m       zero    = proj₂ +-identity m
  m+n∸n≡m zero    (suc n) = m+n∸n≡m zero n
  m+n∸n≡m (suc m) (suc n) = begin
    m + suc n ∸ n
                   ≈⟨ ≡-cong (\x -> x ∸ n) (m+1+n≡1+m+n m n) ⟩
    suc m + n ∸ n
                   ≈⟨ m+n∸n≡m (suc m) n ⟩
    suc m
                   ∎

  m⊓n+n∸m≡n : forall m n -> (m ⊓ n) + (n ∸ m) ≡ n
  m⊓n+n∸m≡n zero    n       = byDef
  m⊓n+n∸m≡n (suc m) zero    = byDef
  m⊓n+n∸m≡n (suc m) (suc n) = ≡-cong suc $ m⊓n+n∸m≡n m n

  -- TODO: Can this proof be simplified? An automatic solver which can
  -- handle ∸ would be nice...

  i∸k∸j+j∸k≡i+j∸k : forall i j k -> i ∸ (k ∸ j) + (j ∸ k) ≡ i + j ∸ k
  i∸k∸j+j∸k≡i+j∸k zero j k = begin
    0 ∸ (k ∸ j) + (j ∸ k)
                           ≈⟨ ≡-cong (\x -> x + (j ∸ k))
                                     (0∸n≡0 (k ∸ j)) ⟩
    0 + (j ∸ k)
                           ≈⟨ byDef ⟩
    j ∸ k
                           ∎
  i∸k∸j+j∸k≡i+j∸k (suc i) j zero = begin
    suc i ∸ (0 ∸ j) + j
                         ≈⟨ ≡-cong (\x -> suc i ∸ x + j) (0∸n≡0 j) ⟩
    suc i ∸ 0 + j
                         ≈⟨ byDef ⟩
    suc (i + j)
                         ∎
  i∸k∸j+j∸k≡i+j∸k (suc i) zero (suc k) = begin
    i ∸ k + 0
               ≈⟨ proj₂ +-identity _ ⟩
    i ∸ k
               ≈⟨ ≡-cong (\x -> x ∸ k)
                         (≡-sym (proj₂ +-identity _)) ⟩
    i + 0 ∸ k
               ∎
  i∸k∸j+j∸k≡i+j∸k (suc i) (suc j) (suc k) = begin
    suc i ∸ (k ∸ j) + (j ∸ k)
                               ≈⟨ i∸k∸j+j∸k≡i+j∸k (suc i) j k ⟩
    suc i + j ∸ k
                               ≈⟨ ≡-cong (\x -> x ∸ k)
                                         (≡-sym (m+1+n≡1+m+n i j)) ⟩
    i + suc j ∸ k
                               ∎

  m+n∸m≡n : forall {m n} -> m ≤ n -> m + (n ∸ m) ≡ n
  m+n∸m≡n z≤n       = byDef
  m+n∸m≡n (s≤s m≤n) = ≡-cong suc $ m+n∸m≡n m≤n

  n≤1+n : forall n -> n ≤ 1 + n
  n≤1+n zero    = z≤n
  n≤1+n (suc n) = s≤s $ n≤1+n n

  n≤m+n : forall m n -> n ≤ m + n
  n≤m+n zero    n = ≤-refl
  n≤m+n (suc m) n =
               start
    n
               ≤⟨ n≤m+n m n ⟩
    m + n
               ≤⟨ n≤1+n _ ⟩
    1 + m + n
               □

  n∸m≤n : forall m n -> n ∸ m ≤ n
  n∸m≤n zero    n       = ≤-refl
  n∸m≤n (suc m) zero    = ≤-refl
  n∸m≤n (suc m) (suc n) = start
    n ∸ m  ≤⟨ n∸m≤n m n ⟩
    n      ≤⟨ n≤1+n n ⟩
    suc n  □

  n≤m+n∸m : forall m n -> n ≤ m + (n ∸ m)
  n≤m+n∸m m       zero    = z≤n
  n≤m+n∸m zero    (suc n) = ≤-refl
  n≤m+n∸m (suc m) (suc n) = s≤s (n≤m+n∸m m n)

  m⊓n≤m : forall m n -> m ⊓ n ≤ m
  m⊓n≤m zero    _       = z≤n
  m⊓n≤m (suc m) zero    = z≤n
  m⊓n≤m (suc m) (suc n) = s≤s $ m⊓n≤m m n

  _+-mono_ : _+_ Preserves₂ _≤_ → _≤_ → _≤_
  _+-mono_ {zero} {m₂} {n₁} {n₂} z≤n n₁≤n₂ = start
    n₁      ≤⟨ n₁≤n₂ ⟩
    n₂      ≤⟨ n≤m+n m₂ n₂ ⟩
    m₂ + n₂ □
  s≤s m₁≤m₂ +-mono n₁≤n₂ = s≤s (m₁≤m₂ +-mono n₁≤n₂)
