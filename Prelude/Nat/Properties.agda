------------------------------------------------------------------------
-- A bunch of arithmetical properties
------------------------------------------------------------------------

module Prelude.Nat.Properties where

open import Prelude.Nat
open import Prelude.Logic
open import Prelude.Function
open import Prelude.BinaryRelation.PropositionalEquality

import Prelude.PreorderProof
private
  open module PP = Prelude.PreorderProof ℕ-preSetoid

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
      suc m + n
    ≃⟨ ≡-refl ⟩
      suc (m + n)
    ≃⟨ ≡-cong suc (+-comm m n) ⟩
      suc (n + m)
    ≃⟨ ≡-sym (m+1+n≡1+m+n n m) ⟩
      n + suc m
    ∎

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
  n*0≡0 (suc n) =
      suc n * 0
    ≃⟨ ≡-refl ⟩
      n * 0 + 0
    ≃⟨ n+0≡n (n * 0) ⟩
      n * 0
    ≃⟨ n*0≡0 n ⟩
      0
    ∎

  m*1+n≡m+mn : forall m n -> m * suc n ≡ m + m * n
  m*1+n≡m+mn zero    n = ≡-refl
  m*1+n≡m+mn (suc m) n =
      suc m * suc n
    ≃⟨ ≡-refl ⟩
      m * suc n + suc n
    ≃⟨ m+1+n≡1+m+n (m * suc n) n ⟩
      suc (m * suc n + n)
    ≃⟨ ≡-cong (\x -> suc (x + n)) (m*1+n≡m+mn m n) ⟩
      suc (m +  m * n + n)
    ≃⟨ ≡-cong suc (≡-sym (+-assoc m (m * n) n)) ⟩
      suc (m + (m * n + n))
    ≃⟨ ≡-refl ⟩
      suc m + suc m * n
    ∎

  *-comm : forall m n -> m * n ≡ n * m
  *-comm zero    n = ≡-sym $ n*0≡0 n
  *-comm (suc m) n =
      suc m * n
    ≃⟨ ≡-refl ⟩
      m * n + n
    ≃⟨ ≡-cong (\x -> x + n) (*-comm m n) ⟩
      n * m + n
    ≃⟨ +-comm (n * m) n ⟩
      n + n * m
    ≃⟨ ≡-sym (m*1+n≡m+mn n m) ⟩
      n * suc m
    ∎

  m*1+n≡m+m*n : forall m n -> m * suc n ≡ m + m * n
  m*1+n≡m+m*n m n =
      m * suc n
    ≃⟨ *-comm m (suc n) ⟩
      suc n * m
    ≃⟨ ≡-refl ⟩
      n * m + m
    ≃⟨ ≡-cong (\x -> x + m) (*-comm n m) ⟩
      m * n + m
    ≃⟨ +-comm (m * n) m ⟩
      m + m * n
    ∎
