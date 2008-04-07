------------------------------------------------------------------------
-- A bunch of properties about natural number operations
------------------------------------------------------------------------

module Data.Nat.Properties where

open import Data.Nat
open ≤-Reasoning
  renaming ( begin_ to start_; _∎ to _□; byDef to ≤-refl
           ; _≡⟨_⟩_ to _≡⟨_⟩'_ )
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
      suc n + m * suc n
    ≈⟨ ≡-cong (\x -> suc n + x) (m*1+n≡m+mn m n) ⟩
      suc n + (m + m * n)
    ≈⟨ byDef ⟩
      suc (n + (m + m * n))
    ≈⟨ ≡-cong suc (≡-sym $ +-assoc n m (m * n)) ⟩
      suc (n + m + m * n)
    ≈⟨ ≡-cong (\x -> suc (x + m * n)) (+-comm n m) ⟩
      suc (m + n + m * n)
    ≈⟨ ≡-cong suc (+-assoc m n (m * n)) ⟩
      suc (m + (n + m * n))
    ≈⟨ byDef ⟩
      suc m + suc m * n
    ∎

  *-zero : Zero 0 _*_
  *-zero = (\_ -> byDef) , n*0≡0
    where
    n*0≡0 : RightZero 0 _*_
    n*0≡0 zero    = byDef
    n*0≡0 (suc n) = n*0≡0 n

  *-comm : Commutative _*_
  *-comm zero    n = ≡-sym $ proj₂ *-zero n
  *-comm (suc m) n =
    begin
      suc m * n
    ≈⟨ byDef ⟩
      n + m * n
    ≈⟨ ≡-cong (\x -> n + x) (*-comm m n) ⟩
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
      (n + o) + m * (n + o)
                                 ≈⟨ ≡-cong (\x -> (n + o) + x) (distˡ m n o) ⟩
      (n + o) + (m * n + m * o)
                                 ≈⟨ ≡-sym $ +-assoc (n + o) (m * n) (m * o) ⟩
      ((n + o) + m * n) + m * o
                                 ≈⟨ ≡-cong (\x -> x + (m * o)) $ +-assoc n o (m * n) ⟩
      (n + (o + m * n)) + m * o
                                 ≈⟨ ≡-cong (\x -> (n + x) + m * o) $ +-comm o (m * n) ⟩
      (n + (m * n + o)) + m * o
                                 ≈⟨ ≡-cong (\x -> x + (m * o)) $ ≡-sym $ +-assoc n (m * n) o ⟩
      ((n + m * n) + o) + m * o
                                 ≈⟨ +-assoc (n + m * n) o (m * o) ⟩
      (n + m * n) + (o + m * o)
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
    (suc m * n) * o
                         ≈⟨ byDef ⟩
    (n + m * n) * o
                         ≈⟨ proj₂ distrib-*-+ o n (m * n) ⟩
    n * o + (m * n) * o
                         ≈⟨ ≡-cong (\x -> n * o + x) $ *-assoc m n o ⟩
    n * o + m * (n * o)
                         ≈⟨ byDef ⟩
    suc m * (n * o)
                         ∎

  *-identity : Identity 1 _*_
  *-identity = proj₂ +-identity , n*1≡n
    where
    n*1≡n : RightIdentity 1 _*_
    n*1≡n n =
      begin
        n * 1
      ≈⟨ *-comm n 1 ⟩
        1 * n
      ≈⟨ byDef ⟩
        n + 0
      ≈⟨ proj₂ +-identity n ⟩
        n
      ∎

ℕ-isCommutativeSemiring : IsCommutativeSemiring ℕ-setoid _+_ _*_ 0 1
ℕ-isCommutativeSemiring = record
  { isSemiring = record
    { isSemiringWithoutAnnihilatingZero = record
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
      }
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
-- (ℕ, ⊔, ⊓, 0) is a commutative semiring without one

private

  ⊔-assoc : Associative _⊔_
  ⊔-assoc zero    _       _       = byDef
  ⊔-assoc (suc m) zero    o       = byDef
  ⊔-assoc (suc m) (suc n) zero    = byDef
  ⊔-assoc (suc m) (suc n) (suc o) = ≡-cong suc $ ⊔-assoc m n o

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

  distrib-⊓-⊔ : _⊓_ DistributesOver _⊔_
  distrib-⊓-⊔ = (distribˡ-⊓-⊔ , distribʳ-⊓-⊔)
    where
    distribʳ-⊓-⊔ : _⊓_ DistributesOverʳ _⊔_
    distribʳ-⊓-⊔ (suc m) (suc n) (suc o) = ≡-cong suc $ distribʳ-⊓-⊔ m n o
    distribʳ-⊓-⊔ (suc m) (suc n) zero    = ≡-cong suc $ byDef
    distribʳ-⊓-⊔ (suc m) zero    o       = byDef
    distribʳ-⊓-⊔ zero    n       o       = begin
      (n ⊔ o) ⊓ 0    ≈⟨ ⊓-comm (n ⊔ o) 0 ⟩
      0 ⊓ (n ⊔ o)    ≈⟨ byDef ⟩
      0 ⊓ n ⊔ 0 ⊓ o  ≈⟨ ⊓-comm 0 n ⟨ ≡-cong₂ _⊔_ ⟩ ⊓-comm 0 o ⟩
      n ⊓ 0 ⊔ o ⊓ 0  ∎

    distribˡ-⊓-⊔ : _⊓_ DistributesOverˡ _⊔_
    distribˡ-⊓-⊔ m n o = begin
      m ⊓ (n ⊔ o)    ≈⟨ ⊓-comm m _ ⟩
      (n ⊔ o) ⊓ m    ≈⟨ distribʳ-⊓-⊔ m n o ⟩
      n ⊓ m ⊔ o ⊓ m  ≈⟨ ⊓-comm n m ⟨ ≡-cong₂ _⊔_ ⟩ ⊓-comm o m ⟩
      m ⊓ n ⊔ m ⊓ o  ∎

ℕ-⊔-⊓-0-isCommutativeSemiringWithoutOne
  : IsCommutativeSemiringWithoutOne ℕ-setoid _⊔_ _⊓_ 0
ℕ-⊔-⊓-0-isCommutativeSemiringWithoutOne = record
  { isSemiringWithoutOne = record
      { +-isCommutativeMonoid = record
          { isMonoid = record
              { isSemigroup = record
                  { assoc = ⊔-assoc
                  ; •-pres-≈ = ≡-cong₂ _⊔_
                  }
              ; identity = ⊔-identity
              }
          ; comm = ⊔-comm
          }
      ; *-isSemigroup = record
          { assoc    = ⊓-assoc
          ; •-pres-≈ = ≡-cong₂ _⊓_
          }
      ; distrib = distrib-⊓-⊔
      ; zero    = ⊓-zero
      }
  ; *-comm = ⊓-comm
  }

ℕ-⊔-⊓-0-commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne
ℕ-⊔-⊓-0-commutativeSemiringWithoutOne = record
  { setoid                          = ℕ-setoid
  ; _+_                             = _⊔_
  ; _*_                             = _⊓_
  ; 0#                              = 0
  ; isCommutativeSemiringWithoutOne =
      ℕ-⊔-⊓-0-isCommutativeSemiringWithoutOne
  }

------------------------------------------------------------------------
-- (ℕ, ⊓, ⊔) is a lattice

private

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
  ; ∨-∧-distribʳ = proj₂ distrib-⊓-⊔
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

-- Converting between ≤ and ≤′.

≤-step : forall {m n} -> m ≤ n -> m ≤ 1 + n
≤-step z≤n       = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

≤′⇒≤ : _≤′_ ⇒ _≤_
≤′⇒≤ ≤′-refl        = ≤-refl
≤′⇒≤ (≤′-step m≤′n) = ≤-step (≤′⇒≤ m≤′n)

z≤′n : forall {n} -> zero ≤′ n
z≤′n {zero}  = ≤′-refl
z≤′n {suc n} = ≤′-step z≤′n

s≤′s : forall {m n} -> m ≤′ n -> suc m ≤′ suc n
s≤′s ≤′-refl        = ≤′-refl
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤⇒≤′ : _≤_ ⇒ _≤′_
≤⇒≤′ z≤n       = z≤′n
≤⇒≤′ (s≤s m≤n) = s≤′s (≤⇒≤′ m≤n)

m≤m+n : forall m n -> m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

m≤′m+n : forall m n -> m ≤′ m + n
m≤′m+n m n = ≤⇒≤′ (m≤m+n m n)

n≤′m+n : forall m n -> n ≤′ m + n
n≤′m+n zero    n = ≤′-refl
n≤′m+n (suc m) n = ≤′-step (n≤′m+n m n)

n≤m+n : forall m n -> n ≤ m + n
n≤m+n m n = ≤′⇒≤ (n≤′m+n m n)

n≤1+n : forall n -> n ≤ 1 + n
n≤1+n _ = ≤-step ≤-refl

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

⌈n/2⌉≤′n : forall n -> ⌈ n /2⌉ ≤′ n
⌈n/2⌉≤′n zero          = ≤′-refl
⌈n/2⌉≤′n (suc zero)    = ≤′-refl
⌈n/2⌉≤′n (suc (suc n)) = s≤′s (≤′-step (⌈n/2⌉≤′n n))

⌊n/2⌋≤′n : forall n -> ⌊ n /2⌋ ≤′ n
⌊n/2⌋≤′n zero    = ≤′-refl
⌊n/2⌋≤′n (suc n) = ≤′-step (⌈n/2⌉≤′n n)

⌊n/2⌋-mono : ⌊_/2⌋ Preserves _≤_ → _≤_
⌊n/2⌋-mono z≤n             = z≤n
⌊n/2⌋-mono (s≤s z≤n)       = z≤n
⌊n/2⌋-mono (s≤s (s≤s m≤n)) = s≤s (⌊n/2⌋-mono m≤n)

⌈n/2⌉-mono : ⌈_/2⌉ Preserves _≤_ → _≤_
⌈n/2⌉-mono m≤n = ⌊n/2⌋-mono (s≤s m≤n)

_+-mono_ : _+_ Preserves₂ _≤_ → _≤_ → _≤_
_+-mono_ {zero} {m₂} {n₁} {n₂} z≤n n₁≤n₂ = start
  n₁      ≤⟨ n₁≤n₂ ⟩
  n₂      ≤⟨ n≤m+n m₂ n₂ ⟩
  m₂ + n₂ □
s≤s m₁≤m₂ +-mono n₁≤n₂ = s≤s (m₁≤m₂ +-mono n₁≤n₂)
