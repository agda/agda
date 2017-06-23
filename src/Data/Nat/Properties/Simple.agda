------------------------------------------------------------------------
-- The Agda standard library
--
-- A bunch of properties about natural number operations
------------------------------------------------------------------------

module Data.Nat.Properties.Simple where

open import Data.Nat.Base as Nat
open import Function
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open PropEq.≡-Reasoning
open import Data.Product
open import Data.Sum

------------------------------------------------------------------------

+-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
+-assoc zero    _ _ = refl
+-assoc (suc m) n o = cong suc $ +-assoc m n o

+-right-identity : ∀ n → n + 0 ≡ n
+-right-identity zero = refl
+-right-identity (suc n) = cong suc $ +-right-identity n

+-left-identity : ∀ n → 0 + n ≡ n
+-left-identity _ = refl

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero    n = sym $ +-right-identity n
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨ refl ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + suc m
  ∎

+-*-suc : ∀ m n → m * suc n ≡ m + m * n
+-*-suc zero    n = refl
+-*-suc (suc m) n =
  begin
    suc m * suc n
  ≡⟨ refl ⟩
    suc n + m * suc n
  ≡⟨ cong (λ x → suc n + x) (+-*-suc m n) ⟩
    suc n + (m + m * n)
  ≡⟨ refl ⟩
    suc (n + (m + m * n))
  ≡⟨ cong suc (sym $ +-assoc n m (m * n)) ⟩
    suc (n + m + m * n)
  ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
    suc (m + n + m * n)
  ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
    suc (m + (n + m * n))
  ≡⟨ refl ⟩
    suc m + suc m * n
  ∎

*-right-zero : ∀ n → n * 0 ≡ 0
*-right-zero zero = refl
*-right-zero (suc n) = *-right-zero n

*-left-zero : ∀ n → 0 * n ≡ 0
*-left-zero _ = refl

*-comm : ∀ m n → m * n ≡ n * m
*-comm zero    n = sym $ *-right-zero n
*-comm (suc m) n =
  begin
    suc m * n
  ≡⟨ refl ⟩
    n + m * n
  ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩
    n + n * m
  ≡⟨ sym (+-*-suc n m) ⟩
    n * suc m
  ∎

distribʳ-*-+ : ∀ m n o → (n + o) * m ≡ n * m + o * m
distribʳ-*-+ m zero    o = refl
distribʳ-*-+ m (suc n) o =
  begin
    (suc n + o) * m
  ≡⟨ refl ⟩
    m + (n + o) * m
  ≡⟨ cong (_+_ m) $ distribʳ-*-+ m n o ⟩
    m + (n * m + o * m)
  ≡⟨ sym $ +-assoc m (n * m) (o * m) ⟩
    m + n * m + o * m
  ≡⟨ refl ⟩
    suc n * m + o * m
  ∎

*-assoc : ∀ m n o → (m * n) * o ≡ m * (n * o)
*-assoc zero    n o = refl
*-assoc (suc m) n o =
  begin
    (suc m * n) * o
  ≡⟨ refl ⟩
    (n + m * n) * o
  ≡⟨ distribʳ-*-+ o n (m * n) ⟩
    n * o + (m * n) * o
  ≡⟨ cong (λ x → n * o + x) $ *-assoc m n o ⟩
    n * o + m * (n * o)
  ≡⟨ refl ⟩
    suc m * (n * o)
  ∎
