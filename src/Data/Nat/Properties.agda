------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties about natural number operations
------------------------------------------------------------------------

-- See README.Nat for some examples showing how this module can be
-- used.

module Data.Nat.Properties where

open import Data.Nat as Nat
open ≤-Reasoning
  renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
open import Relation.Binary
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
open import Function
open import Algebra
open import Algebra.Structures
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
import Algebra.FunctionProperties as P; open P (_≡_ {A = ℕ})
open import Data.Product
open import Data.Sum

------------------------------------------------------------------------

-- basic lemmas about (ℕ, +, *, 0, 1):
open import Data.Nat.Properties.Simple

-- (ℕ, +, *, 0, 1) is a commutative semiring
isCommutativeSemiring : IsCommutativeSemiring _≡_ _+_ _*_ 0 1
isCommutativeSemiring = record
  { +-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc         = +-assoc
      ; ∙-cong        = cong₂ _+_
      }
    ; identityˡ = λ _ → refl
    ; comm      = +-comm
    }
  ; *-isCommutativeMonoid = record
    { isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc         = *-assoc
      ; ∙-cong        = cong₂ _*_
      }
    ; identityˡ = +-right-identity
    ; comm      = *-comm
    }
  ; distribʳ = distribʳ-*-+
  ; zeroˡ    = λ _ → refl
  }

commutativeSemiring : CommutativeSemiring _ _
commutativeSemiring = record
  { _+_                   = _+_
  ; _*_                   = _*_
  ; 0#                    = 0
  ; 1#                    = 1
  ; isCommutativeSemiring = isCommutativeSemiring
  }

import Algebra.RingSolver.Simple as Solver
import Algebra.RingSolver.AlmostCommutativeRing as ACR
module SemiringSolver =
  Solver (ACR.fromCommutativeSemiring commutativeSemiring) _≟_

------------------------------------------------------------------------
-- (ℕ, ⊔, ⊓, 0) is a commutative semiring without one

private

  ⊔-assoc : Associative _⊔_
  ⊔-assoc zero    _       _       = refl
  ⊔-assoc (suc m) zero    o       = refl
  ⊔-assoc (suc m) (suc n) zero    = refl
  ⊔-assoc (suc m) (suc n) (suc o) = cong suc $ ⊔-assoc m n o

  ⊔-identity : Identity 0 _⊔_
  ⊔-identity = (λ _ → refl) , n⊔0≡n
    where
    n⊔0≡n : RightIdentity 0 _⊔_
    n⊔0≡n zero    = refl
    n⊔0≡n (suc n) = refl

  ⊔-comm : Commutative _⊔_
  ⊔-comm zero    n       = sym $ proj₂ ⊔-identity n
  ⊔-comm (suc m) zero    = refl
  ⊔-comm (suc m) (suc n) =
    begin
      suc m ⊔ suc n
    ≡⟨ refl ⟩
      suc (m ⊔ n)
    ≡⟨ cong suc (⊔-comm m n) ⟩
      suc (n ⊔ m)
    ≡⟨ refl ⟩
      suc n ⊔ suc m
    ∎

  ⊓-assoc : Associative _⊓_
  ⊓-assoc zero    _       _       = refl
  ⊓-assoc (suc m) zero    o       = refl
  ⊓-assoc (suc m) (suc n) zero    = refl
  ⊓-assoc (suc m) (suc n) (suc o) = cong suc $ ⊓-assoc m n o

  ⊓-zero : Zero 0 _⊓_
  ⊓-zero = (λ _ → refl) , n⊓0≡0
    where
    n⊓0≡0 : RightZero 0 _⊓_
    n⊓0≡0 zero    = refl
    n⊓0≡0 (suc n) = refl

  ⊓-comm : Commutative _⊓_
  ⊓-comm zero    n       = sym $ proj₂ ⊓-zero n
  ⊓-comm (suc m) zero    = refl
  ⊓-comm (suc m) (suc n) =
    begin
      suc m ⊓ suc n
    ≡⟨ refl ⟩
      suc (m ⊓ n)
    ≡⟨ cong suc (⊓-comm m n) ⟩
      suc (n ⊓ m)
    ≡⟨ refl ⟩
      suc n ⊓ suc m
    ∎

  distrib-⊓-⊔ : _⊓_ DistributesOver _⊔_
  distrib-⊓-⊔ = (distribˡ-⊓-⊔ , distribʳ-⊓-⊔)
    where
    distribʳ-⊓-⊔ : _⊓_ DistributesOverʳ _⊔_
    distribʳ-⊓-⊔ (suc m) (suc n) (suc o) = cong suc $ distribʳ-⊓-⊔ m n o
    distribʳ-⊓-⊔ (suc m) (suc n) zero    = cong suc $ refl
    distribʳ-⊓-⊔ (suc m) zero    o       = refl
    distribʳ-⊓-⊔ zero    n       o       = begin
      (n ⊔ o) ⊓ 0    ≡⟨ ⊓-comm (n ⊔ o) 0 ⟩
      0 ⊓ (n ⊔ o)    ≡⟨ refl ⟩
      0 ⊓ n ⊔ 0 ⊓ o  ≡⟨ ⊓-comm 0 n ⟨ cong₂ _⊔_ ⟩ ⊓-comm 0 o ⟩
      n ⊓ 0 ⊔ o ⊓ 0  ∎

    distribˡ-⊓-⊔ : _⊓_ DistributesOverˡ _⊔_
    distribˡ-⊓-⊔ m n o = begin
      m ⊓ (n ⊔ o)    ≡⟨ ⊓-comm m _ ⟩
      (n ⊔ o) ⊓ m    ≡⟨ distribʳ-⊓-⊔ m n o ⟩
      n ⊓ m ⊔ o ⊓ m  ≡⟨ ⊓-comm n m ⟨ cong₂ _⊔_ ⟩ ⊓-comm o m ⟩
      m ⊓ n ⊔ m ⊓ o  ∎

⊔-⊓-0-isCommutativeSemiringWithoutOne
  : IsCommutativeSemiringWithoutOne _≡_ _⊔_ _⊓_ 0
⊔-⊓-0-isCommutativeSemiringWithoutOne = record
  { isSemiringWithoutOne = record
    { +-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = PropEq.isEquivalence
        ; assoc         = ⊔-assoc
        ; ∙-cong        = cong₂ _⊔_
        }
      ; identityˡ = proj₁ ⊔-identity
      ; comm      = ⊔-comm
      }
    ; *-isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc         = ⊓-assoc
      ; ∙-cong        = cong₂ _⊓_
      }
    ; distrib = distrib-⊓-⊔
    ; zero    = ⊓-zero
    }
  ; *-comm = ⊓-comm
  }

⊔-⊓-0-commutativeSemiringWithoutOne : CommutativeSemiringWithoutOne _ _
⊔-⊓-0-commutativeSemiringWithoutOne = record
  { _+_                             = _⊔_
  ; _*_                             = _⊓_
  ; 0#                              = 0
  ; isCommutativeSemiringWithoutOne =
      ⊔-⊓-0-isCommutativeSemiringWithoutOne
  }

------------------------------------------------------------------------
-- (ℕ, ⊓, ⊔) is a lattice

private

  absorptive-⊓-⊔ : Absorptive _⊓_ _⊔_
  absorptive-⊓-⊔ = abs-⊓-⊔ , abs-⊔-⊓
    where
    abs-⊔-⊓ : _⊔_ Absorbs _⊓_
    abs-⊔-⊓ zero    n       = refl
    abs-⊔-⊓ (suc m) zero    = refl
    abs-⊔-⊓ (suc m) (suc n) = cong suc $ abs-⊔-⊓ m n

    abs-⊓-⊔ : _⊓_ Absorbs _⊔_
    abs-⊓-⊔ zero    n       = refl
    abs-⊓-⊔ (suc m) (suc n) = cong suc $ abs-⊓-⊔ m n
    abs-⊓-⊔ (suc m) zero    = cong suc $
                   begin
      m ⊓ m
                   ≡⟨ cong (_⊓_ m) $ sym $ proj₂ ⊔-identity m ⟩
      m ⊓ (m ⊔ 0)
                   ≡⟨ abs-⊓-⊔ m zero ⟩
      m
                   ∎

isDistributiveLattice : IsDistributiveLattice _≡_ _⊓_ _⊔_
isDistributiveLattice = record
  { isLattice = record
      { isEquivalence = PropEq.isEquivalence
      ; ∨-comm        = ⊓-comm
      ; ∨-assoc       = ⊓-assoc
      ; ∨-cong        = cong₂ _⊓_
      ; ∧-comm        = ⊔-comm
      ; ∧-assoc       = ⊔-assoc
      ; ∧-cong        = cong₂ _⊔_
      ; absorptive    = absorptive-⊓-⊔
      }
  ; ∨-∧-distribʳ = proj₂ distrib-⊓-⊔
  }

distributiveLattice : DistributiveLattice _ _
distributiveLattice = record
  { _∨_                   = _⊓_
  ; _∧_                   = _⊔_
  ; isDistributiveLattice = isDistributiveLattice
  }

-- Selectivity and idempotence of ⊓ and ⊔

-- ∀ x y → (x ⊓ y ≡ x) ⊎ (x ⊓ y ≡ y)

⊓-sel : Selective _⊓_
⊓-sel zero    _    = inj₁ refl
⊓-sel (suc m) zero = inj₂ refl
⊓-sel (suc m) (suc n) with ⊓-sel m n
... | inj₁ m⊓n≡m = inj₁ (cong suc m⊓n≡m)
... | inj₂ m⊓n≡n = inj₂ (cong suc m⊓n≡n)

-- ∀ x y → (x ⊔ y ≡ x) ⊎ (x ⊔ y ≡ y)

⊔-sel : Selective _⊔_
⊔-sel zero    _    = inj₂ refl
⊔-sel (suc m) zero = inj₁ refl
⊔-sel (suc m) (suc n) with ⊔-sel m n
... | inj₁ m⊔n≡m = inj₁ (cong suc m⊔n≡m)
... | inj₂ m⊔n≡n = inj₂ (cong suc m⊔n≡n)

-- ∀ x → x ⊓ x ≡ x

⊓-idem : Idempotent _⊓_
⊓-idem x with ⊓-sel x x
... | inj₁ x⊓x≈x = x⊓x≈x
... | inj₂ x⊓x≈x = x⊓x≈x

-- ∀ x → x ⊔ x ≡ x

⊔-idem : Idempotent _⊔_
⊔-idem x with ⊔-sel x x
... | inj₁ x⊔x≈x = x⊔x≈x
... | inj₂ x⊔x≈x = x⊔x≈x

------------------------------------------------------------------------
-- Converting between ≤ and ≤′

≤-step : ∀ {m n} → m ≤ n → m ≤ 1 + n
≤-step z≤n       = z≤n
≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

≤′⇒≤ : _≤′_ ⇒ _≤_
≤′⇒≤ ≤′-refl        = ≤-refl
≤′⇒≤ (≤′-step m≤′n) = ≤-step (≤′⇒≤ m≤′n)

z≤′n : ∀ {n} → zero ≤′ n
z≤′n {zero}  = ≤′-refl
z≤′n {suc n} = ≤′-step z≤′n

s≤′s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
s≤′s ≤′-refl        = ≤′-refl
s≤′s (≤′-step m≤′n) = ≤′-step (s≤′s m≤′n)

≤⇒≤′ : _≤_ ⇒ _≤′_
≤⇒≤′ z≤n       = z≤′n
≤⇒≤′ (s≤s m≤n) = s≤′s (≤⇒≤′ m≤n)

------------------------------------------------------------------------
-- Various order-related properties

≤-steps : ∀ {m n} k → m ≤ n → m ≤ k + n
≤-steps zero    m≤n = m≤n
≤-steps (suc k) m≤n = ≤-step (≤-steps k m≤n)

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero    n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

m≤′m+n : ∀ m n → m ≤′ m + n
m≤′m+n m n = ≤⇒≤′ (m≤m+n m n)

n≤′m+n : ∀ m n → n ≤′ m + n
n≤′m+n zero    n = ≤′-refl
n≤′m+n (suc m) n = ≤′-step (n≤′m+n m n)

n≤m+n : ∀ m n → n ≤ m + n
n≤m+n m n = ≤′⇒≤ (n≤′m+n m n)

n≤1+n : ∀ n → n ≤ 1 + n
n≤1+n _ = ≤-step ≤-refl

1+n≰n : ∀ {n} → ¬ 1 + n ≤ n
1+n≰n (s≤s le) = 1+n≰n le

≤pred⇒≤ : ∀ m n → m ≤ pred n → m ≤ n
≤pred⇒≤ m zero    le = le
≤pred⇒≤ m (suc n) le = ≤-step le

≤⇒pred≤ : ∀ m n → m ≤ n → pred m ≤ n
≤⇒pred≤ zero    n le = le
≤⇒pred≤ (suc m) n le = start
  m     ≤⟨ n≤1+n m ⟩
  suc m ≤⟨ le ⟩
  n     □

<⇒≤pred : ∀ {m n} → m < n → m ≤ pred n
<⇒≤pred (s≤s le) = le

¬i+1+j≤i : ∀ i {j} → ¬ i + suc j ≤ i
¬i+1+j≤i zero    ()
¬i+1+j≤i (suc i) le = ¬i+1+j≤i i (≤-pred le)

n∸m≤n : ∀ m n → n ∸ m ≤ n
n∸m≤n zero    n       = ≤-refl
n∸m≤n (suc m) zero    = ≤-refl
n∸m≤n (suc m) (suc n) = start
  n ∸ m  ≤⟨ n∸m≤n m n ⟩
  n      ≤⟨ n≤1+n n ⟩
  suc n  □

n≤m+n∸m : ∀ m n → n ≤ m + (n ∸ m)
n≤m+n∸m m       zero    = z≤n
n≤m+n∸m zero    (suc n) = ≤-refl
n≤m+n∸m (suc m) (suc n) = s≤s (n≤m+n∸m m n)

m⊓n≤m : ∀ m n → m ⊓ n ≤ m
m⊓n≤m zero    _       = z≤n
m⊓n≤m (suc m) zero    = z≤n
m⊓n≤m (suc m) (suc n) = s≤s $ m⊓n≤m m n

m≤m⊔n : ∀ m n → m ≤ m ⊔ n
m≤m⊔n zero    _       = z≤n
m≤m⊔n (suc m) zero    = ≤-refl
m≤m⊔n (suc m) (suc n) = s≤s $ m≤m⊔n m n

⌈n/2⌉≤′n : ∀ n → ⌈ n /2⌉ ≤′ n
⌈n/2⌉≤′n zero          = ≤′-refl
⌈n/2⌉≤′n (suc zero)    = ≤′-refl
⌈n/2⌉≤′n (suc (suc n)) = s≤′s (≤′-step (⌈n/2⌉≤′n n))

⌊n/2⌋≤′n : ∀ n → ⌊ n /2⌋ ≤′ n
⌊n/2⌋≤′n zero    = ≤′-refl
⌊n/2⌋≤′n (suc n) = ≤′-step (⌈n/2⌉≤′n n)

<-trans : Transitive _<_
<-trans {i} {j} {k} i<j j<k = start
  1 + i  ≤⟨ i<j ⟩
  j      ≤⟨ n≤1+n j ⟩
  1 + j  ≤⟨ j<k ⟩
  k      □

≰⇒> : _≰_ ⇒ _>_
≰⇒> {zero}          z≰n with z≰n z≤n
... | ()
≰⇒> {suc m} {zero}  _   = s≤s z≤n
≰⇒> {suc m} {suc n} m≰n = s≤s (≰⇒> (m≰n ∘ s≤s))

------------------------------------------------------------------------
-- Converting between ≤ and ≤″

≤″⇒≤ : _≤″_ ⇒ _≤_
≤″⇒≤ (less-than-or-equal refl) = m≤m+n _ _

≤⇒≤″ : _≤_ ⇒ _≤″_
≤⇒≤″ m≤n = less-than-or-equal (proof m≤n)
  where
  k : ∀ m n → m ≤ n → ℕ
  k zero    n       _   = n
  k (suc m) zero    ()
  k (suc m) (suc n) m≤n = k m n (≤-pred m≤n)

  proof : ∀ {m n} (m≤n : m ≤ n) → m + k m n m≤n ≡ n
  proof z≤n       = refl
  proof (s≤s m≤n) = cong suc (proof m≤n)

------------------------------------------------------------------------
-- (ℕ, _≡_, _<_) is a strict total order

m≢1+m+n : ∀ m {n} → m ≢ suc (m + n)
m≢1+m+n zero    ()
m≢1+m+n (suc m) eq = m≢1+m+n m (cong pred eq)

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = record
  { Carrier            = ℕ
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = record
    { isEquivalence = PropEq.isEquivalence
    ; trans         = <-trans
    ; compare       = cmp
    }
  }
  where
  2+m+n≰m : ∀ {m n} → ¬ 2 + (m + n) ≤ m
  2+m+n≰m (s≤s le) = 2+m+n≰m le

  cmp : Trichotomous _≡_ _<_
  cmp m n with compare m n
  cmp .m .(suc (m + k)) | less    m k = tri< (m≤m+n (suc m) k) (m≢1+m+n _) 2+m+n≰m
  cmp .n             .n | equal   n   = tri≈ 1+n≰n refl 1+n≰n
  cmp .(suc (n + k)) .n | greater n k = tri> 2+m+n≰m (m≢1+m+n _ ∘ sym) (m≤m+n (suc n) k)

------------------------------------------------------------------------
-- Miscellaneous other properties

0∸n≡0 : LeftZero zero _∸_
0∸n≡0 zero    = refl
0∸n≡0 (suc _) = refl

n∸n≡0 : ∀ n → n ∸ n ≡ 0
n∸n≡0 zero    = refl
n∸n≡0 (suc n) = n∸n≡0 n

∸-+-assoc : ∀ m n o → (m ∸ n) ∸ o ≡ m ∸ (n + o)
∸-+-assoc m       n       zero    = cong (_∸_ m) (sym $ +-right-identity n)
∸-+-assoc zero    zero    (suc o) = refl
∸-+-assoc zero    (suc n) (suc o) = refl
∸-+-assoc (suc m) zero    (suc o) = refl
∸-+-assoc (suc m) (suc n) (suc o) = ∸-+-assoc m n (suc o)

+-∸-assoc : ∀ m {n o} → o ≤ n → (m + n) ∸ o ≡ m + (n ∸ o)
+-∸-assoc m (z≤n {n = n})             = begin m + n ∎
+-∸-assoc m (s≤s {m = o} {n = n} o≤n) = begin
  (m + suc n) ∸ suc o  ≡⟨ cong (λ n → n ∸ suc o) (+-suc m n) ⟩
  suc (m + n) ∸ suc o  ≡⟨ refl ⟩
  (m + n) ∸ o          ≡⟨ +-∸-assoc m o≤n ⟩
  m + (n ∸ o)          ∎

m+n∸n≡m : ∀ m n → (m + n) ∸ n ≡ m
m+n∸n≡m m n = begin
  (m + n) ∸ n  ≡⟨ +-∸-assoc m (≤-refl {x = n}) ⟩
  m + (n ∸ n)  ≡⟨ cong (_+_ m) (n∸n≡0 n) ⟩
  m + 0        ≡⟨ +-right-identity m ⟩
  m            ∎

m+n∸m≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m+n∸m≡n {m} {n} m≤n = begin
  m + (n ∸ m)  ≡⟨ sym $ +-∸-assoc m m≤n ⟩
  (m + n) ∸ m  ≡⟨ cong (λ n → n ∸ m) (+-comm m n) ⟩
  (n + m) ∸ m  ≡⟨ m+n∸n≡m n m ⟩
  n            ∎

m⊓n+n∸m≡n : ∀ m n → (m ⊓ n) + (n ∸ m) ≡ n
m⊓n+n∸m≡n zero    n       = refl
m⊓n+n∸m≡n (suc m) zero    = refl
m⊓n+n∸m≡n (suc m) (suc n) = cong suc $ m⊓n+n∸m≡n m n

[m∸n]⊓[n∸m]≡0 : ∀ m n → (m ∸ n) ⊓ (n ∸ m) ≡ 0
[m∸n]⊓[n∸m]≡0 zero zero       = refl
[m∸n]⊓[n∸m]≡0 zero (suc n)    = refl
[m∸n]⊓[n∸m]≡0 (suc m) zero    = refl
[m∸n]⊓[n∸m]≡0 (suc m) (suc n) = [m∸n]⊓[n∸m]≡0 m n

[i+j]∸[i+k]≡j∸k : ∀ i j k → (i + j) ∸ (i + k) ≡ j ∸ k
[i+j]∸[i+k]≡j∸k zero    j k = refl
[i+j]∸[i+k]≡j∸k (suc i) j k = [i+j]∸[i+k]≡j∸k i j k

-- TODO: Can this proof be simplified? An automatic solver which can
-- handle ∸ would be nice...

i∸k∸j+j∸k≡i+j∸k : ∀ i j k → i ∸ (k ∸ j) + (j ∸ k) ≡ i + j ∸ k
i∸k∸j+j∸k≡i+j∸k zero j k = begin
  0 ∸ (k ∸ j) + (j ∸ k)
                         ≡⟨ cong (λ x → x + (j ∸ k)) (0∸n≡0 (k ∸ j)) ⟩
  0 + (j ∸ k)
                         ≡⟨ refl ⟩
  j ∸ k
                         ∎
i∸k∸j+j∸k≡i+j∸k (suc i) j zero = begin
  suc i ∸ (0 ∸ j) + j
                       ≡⟨ cong (λ x → suc i ∸ x + j) (0∸n≡0 j) ⟩
  suc i ∸ 0 + j
                       ≡⟨ refl ⟩
  suc (i + j)
                       ∎
i∸k∸j+j∸k≡i+j∸k (suc i) zero (suc k) = begin
  i ∸ k + 0
             ≡⟨ +-right-identity _ ⟩
  i ∸ k
             ≡⟨ cong (λ x → x ∸ k) (sym (+-right-identity _)) ⟩
  i + 0 ∸ k
             ∎
i∸k∸j+j∸k≡i+j∸k (suc i) (suc j) (suc k) = begin
  suc i ∸ (k ∸ j) + (j ∸ k)
                             ≡⟨ i∸k∸j+j∸k≡i+j∸k (suc i) j k ⟩
  suc i + j ∸ k
                             ≡⟨ cong (λ x → x ∸ k)
                                     (sym (+-suc i j)) ⟩
  i + suc j ∸ k
                             ∎

i+j≡0⇒i≡0 : ∀ i {j} → i + j ≡ 0 → i ≡ 0
i+j≡0⇒i≡0 zero    eq = refl
i+j≡0⇒i≡0 (suc i) ()

i+j≡0⇒j≡0 : ∀ i {j} → i + j ≡ 0 → j ≡ 0
i+j≡0⇒j≡0 i {j} i+j≡0 = i+j≡0⇒i≡0 j $ begin
  j + i
    ≡⟨ +-comm j i ⟩
  i + j
    ≡⟨ i+j≡0 ⟩
  0
    ∎

i*j≡0⇒i≡0∨j≡0 : ∀ i {j} → i * j ≡ 0 → i ≡ 0 ⊎ j ≡ 0
i*j≡0⇒i≡0∨j≡0 zero    {j}     eq = inj₁ refl
i*j≡0⇒i≡0∨j≡0 (suc i) {zero}  eq = inj₂ refl
i*j≡0⇒i≡0∨j≡0 (suc i) {suc j} ()

i*j≡1⇒i≡1 : ∀ i j → i * j ≡ 1 → i ≡ 1
i*j≡1⇒i≡1 (suc zero)    j             _  = refl
i*j≡1⇒i≡1 zero          j             ()
i*j≡1⇒i≡1 (suc (suc i)) (suc (suc j)) ()
i*j≡1⇒i≡1 (suc (suc i)) (suc zero)    ()
i*j≡1⇒i≡1 (suc (suc i)) zero          eq with begin
  0      ≡⟨ *-comm 0 i ⟩
  i * 0  ≡⟨ eq ⟩
  1      ∎
... | ()

i*j≡1⇒j≡1 : ∀ i j → i * j ≡ 1 → j ≡ 1
i*j≡1⇒j≡1 i j eq = i*j≡1⇒i≡1 j i (begin
  j * i  ≡⟨ *-comm j i ⟩
  i * j  ≡⟨ eq ⟩
  1      ∎)

cancel-+-left : ∀ i {j k} → i + j ≡ i + k → j ≡ k
cancel-+-left zero    eq = eq
cancel-+-left (suc i) eq = cancel-+-left i (cong pred eq)

cancel-+-left-≤ : ∀ i {j k} → i + j ≤ i + k → j ≤ k
cancel-+-left-≤ zero    le       = le
cancel-+-left-≤ (suc i) (s≤s le) = cancel-+-left-≤ i le

cancel-*-right : ∀ i j {k} → i * suc k ≡ j * suc k → i ≡ j
cancel-*-right zero    zero        eq = refl
cancel-*-right zero    (suc j)     ()
cancel-*-right (suc i) zero        ()
cancel-*-right (suc i) (suc j) {k} eq =
  cong suc (cancel-*-right i j (cancel-+-left (suc k) eq))

cancel-*-right-≤ : ∀ i j k → i * suc k ≤ j * suc k → i ≤ j
cancel-*-right-≤ zero    _       _ _  = z≤n
cancel-*-right-≤ (suc i) zero    _ ()
cancel-*-right-≤ (suc i) (suc j) k le =
  s≤s (cancel-*-right-≤ i j k (cancel-+-left-≤ (suc k) le))

*-distrib-∸ʳ : _*_ DistributesOverʳ _∸_
*-distrib-∸ʳ i zero k = begin
  (0 ∸ k) * i  ≡⟨ cong₂ _*_ (0∸n≡0 k) refl ⟩
  0            ≡⟨ sym $ 0∸n≡0 (k * i) ⟩
  0 ∸ k * i    ∎
*-distrib-∸ʳ i (suc j) zero    = begin i + j * i ∎
*-distrib-∸ʳ i (suc j) (suc k) = begin
  (j ∸ k) * i             ≡⟨ *-distrib-∸ʳ i j k ⟩
  j * i ∸ k * i           ≡⟨ sym $ [i+j]∸[i+k]≡j∸k i _ _ ⟩
  i + j * i ∸ (i + k * i) ∎

im≡jm+n⇒[i∸j]m≡n
  : ∀ i j m n →
    i * m ≡ j * m + n → (i ∸ j) * m ≡ n
im≡jm+n⇒[i∸j]m≡n i j m n eq = begin
  (i ∸ j) * m            ≡⟨ *-distrib-∸ʳ m i j ⟩
  (i * m) ∸ (j * m)      ≡⟨ cong₂ _∸_ eq (refl {x = j * m}) ⟩
  (j * m + n) ∸ (j * m)  ≡⟨ cong₂ _∸_ (+-comm (j * m) n) (refl {x = j * m}) ⟩
  (n + j * m) ∸ (j * m)  ≡⟨ m+n∸n≡m n (j * m) ⟩
  n                      ∎

i+1+j≢i : ∀ i {j} → i + suc j ≢ i
i+1+j≢i i eq = ¬i+1+j≤i i (reflexive eq)
  where open DecTotalOrder decTotalOrder

⌊n/2⌋-mono : ⌊_/2⌋ Preserves _≤_ ⟶ _≤_
⌊n/2⌋-mono z≤n             = z≤n
⌊n/2⌋-mono (s≤s z≤n)       = z≤n
⌊n/2⌋-mono (s≤s (s≤s m≤n)) = s≤s (⌊n/2⌋-mono m≤n)

⌈n/2⌉-mono : ⌈_/2⌉ Preserves _≤_ ⟶ _≤_
⌈n/2⌉-mono m≤n = ⌊n/2⌋-mono (s≤s m≤n)

pred-mono : pred Preserves _≤_ ⟶ _≤_
pred-mono z≤n      = z≤n
pred-mono (s≤s le) = le

_+-mono_ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
_+-mono_ {zero} {m₂} {n₁} {n₂} z≤n n₁≤n₂ = start
  n₁      ≤⟨ n₁≤n₂ ⟩
  n₂      ≤⟨ n≤m+n m₂ n₂ ⟩
  m₂ + n₂ □
s≤s m₁≤m₂ +-mono n₁≤n₂ = s≤s (m₁≤m₂ +-mono n₁≤n₂)

_*-mono_ : _*_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
z≤n       *-mono n₁≤n₂ = z≤n
s≤s m₁≤m₂ *-mono n₁≤n₂ = n₁≤n₂ +-mono (m₁≤m₂ *-mono n₁≤n₂)

∸-mono : _∸_ Preserves₂ _≤_ ⟶ _≥_ ⟶ _≤_
∸-mono           z≤n         (s≤s n₁≥n₂)    = z≤n
∸-mono           (s≤s m₁≤m₂) (s≤s n₁≥n₂)    = ∸-mono m₁≤m₂ n₁≥n₂
∸-mono {m₁} {m₂} m₁≤m₂       (z≤n {n = n₁}) = start
  m₁ ∸ n₁  ≤⟨ n∸m≤n n₁ m₁ ⟩
  m₁       ≤⟨ m₁≤m₂ ⟩
  m₂       □
