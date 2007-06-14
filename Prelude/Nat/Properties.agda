------------------------------------------------------------------------
-- A bunch of arithmetical properties
------------------------------------------------------------------------

module Prelude.Nat.Properties where

open import Prelude.Nat
open import Prelude.Logic
open import Prelude.Function
open import Prelude.BinaryRelation.PropositionalEquality

abstract

  n+0≡n : forall n -> n + 0 ≡ n
  n+0≡n zero    = ≡-refl
  n+0≡n (suc n) = ≡-cong suc $ n+0≡n n

  +-assoc : forall m n o -> m + (n + o) ≡ (m + n) + o
  +-assoc zero    _ _ = ≡-refl
  +-assoc (suc m) n o = ≡-cong suc $ +-assoc m n o

  m+1+n≡1+m+n : forall m n -> m + suc n ≡ suc (m + n)
  m+1+n≡1+m+n zero    n = ≡-refl
  m+1+n≡1+m+n (suc m) n = ≡-cong suc (m+1+n≡1+m+n m n)

  +-comm : forall m n -> m + n ≡ n + m
  +-comm zero    n = ≡-sym $ n+0≡n n
  +-comm (suc m) n =
    ≡-cong suc (+-comm m n)
      ⟨ ≡-trans ⟩
    ≡-sym (m+1+n≡1+m+n n m)

  0∸n≡0 : forall n -> zero ∸ n ≡ zero
  0∸n≡0 zero    = ≡-refl
  0∸n≡0 (suc _) = ≡-refl

  ∸-+-assoc : forall m n o -> (m ∸ n) ∸ o ≡ m ∸ (n + o)
  ∸-+-assoc m       n       zero    = ≡-cong (_∸_ m) (≡-sym $ n+0≡n n)
  ∸-+-assoc zero    zero    (suc o) = ≡-refl
  ∸-+-assoc zero    (suc n) (suc o) = ≡-refl
  ∸-+-assoc (suc m) zero    (suc o) = ≡-refl
  ∸-+-assoc (suc m) (suc n) (suc o) = ∸-+-assoc m n (suc o)

  n*0≡0 : forall n -> n * 0 ≡ 0
  n*0≡0 zero    = ≡-refl
  n*0≡0 (suc n) = n+0≡n (n * 0) ⟨ ≡-trans ⟩ n*0≡0 n

  m*1+n≡m+mn : forall m n -> m * suc n ≡ m + m * n
  m*1+n≡m+mn zero    n = ≡-refl
  m*1+n≡m+mn (suc m) n =
    m+1+n≡1+m+n (m * suc n) n
      ⟨ ≡-trans ⟩
    ≡-cong suc (≡-cong (\x -> x + n) (m*1+n≡m+mn m n)
                  ⟨ ≡-trans ⟩
                ≡-sym (+-assoc m (m * n) n))

  *-comm : forall m n -> m * n ≡ n * m
  *-comm zero    n = ≡-sym $ n*0≡0 n
  *-comm (suc m) n =
    ≡-cong (\x -> x + n) (*-comm m n)
      ⟨ ≡-trans ⟩
    +-comm (n * m) n
      ⟨ ≡-trans ⟩
    ≡-sym (m*1+n≡m+mn n m)

  m*1+n≡m+m*n : forall m n -> m * suc n ≡ m + m * n
  m*1+n≡m+m*n m n =
    *-comm m (suc n)
      ⟨ ≡-trans ⟩
    ≡-cong (\x -> x + m) (*-comm n m)
      ⟨ ≡-trans ⟩
    +-comm (m * n) m
