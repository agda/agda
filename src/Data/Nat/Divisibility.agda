------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility
------------------------------------------------------------------------

module Data.Nat.Divisibility where

open import Data.Nat as Nat
open import Data.Nat.DivMod
open import Data.Nat.Properties
open import Data.Fin using (Fin; zero; suc; toℕ)
import Data.Fin.Properties as FP
open SemiringSolver
open import Algebra
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PartialOrderReasoning as PartialOrderReasoning
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Function

------------------------------------------------------------------------
-- m ∣ n is inhabited iff m divides n. Some sources, like Hardy and
-- Wright's "An Introduction to the Theory of Numbers", require m to
-- be non-zero. However, some things become a bit nicer if m is
-- allowed to be zero. For instance, _∣_ becomes a partial order, and
-- the gcd of 0 and 0 becomes defined.

infix 4 _∣_ _∤_

record _∣_ (m n : ℕ) : Set where
  constructor divides
  field quotient : ℕ
        equality : n ≡ quotient * m

_∤_ : Rel ℕ _
m ∤ n = ¬ (m ∣ n)

quotient : ∀ {m n} → m ∣ n → ℕ
quotient (divides q _) = q

------------------------------------------------------------------------
-- _∣_ is a partial order

∣⇒≤ : ∀ {m n} → m ∣ suc n → m ≤ suc n
∣⇒≤         (divides zero    ())
∣⇒≤ {m} {n} (divides (suc q) eq) = begin
  m          ≤⟨ m≤m+n m (q * m) ⟩
  suc q * m  ≡⟨ sym eq ⟩
  suc n      ∎
  where open ≤-Reasoning

∣-reflexive : _≡_ ⇒ _∣_
∣-reflexive {n} refl = divides 1 (sym (*-identityˡ n))

∣-refl : Reflexive _∣_
∣-refl = ∣-reflexive refl

∣-trans : Transitive _∣_
∣-trans (divides p refl) (divides q refl) =
  divides (q * p) (sym (*-assoc q p _))

∣-antisym : Antisymmetric _≡_ _∣_
∣-antisym {m} {0} _ (divides q eq) = trans eq (*-comm q 0)
∣-antisym {0} {n} (divides p eq) _ = sym (trans eq (*-comm p 0))
∣-antisym {suc m} {suc n} (divides p eq₁) (divides q eq₂) =
  ≤-antisym (∣⇒≤ (divides p eq₁)) (∣⇒≤ (divides q eq₂))

∣-isPreorder : IsPreorder _≡_ _∣_
∣-isPreorder = record
  { isEquivalence = PropEq.isEquivalence
  ; reflexive     = ∣-reflexive
  ; trans         = ∣-trans
  }

∣-isPartialOrder : IsPartialOrder _≡_ _∣_
∣-isPartialOrder = record
  { isPreorder = ∣-isPreorder
  ; antisym    = ∣-antisym
  }

poset : Poset _ _ _
poset = record
  { Carrier        = ℕ
  ; _≈_            = _≡_
  ; _≤_            = _∣_
  ; isPartialOrder = ∣-isPartialOrder
  }

module ∣-Reasoning = PartialOrderReasoning poset
  renaming (_≤⟨_⟩_ to _∣⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

------------------------------------------------------------------------
-- Simple properties of _∣_

infix 10 1∣_ _∣0

1∣_ : ∀ n → 1 ∣ n
1∣ n = divides n (sym (*-identityʳ n))

_∣0 : ∀ n → n ∣ 0
n ∣0 = divides 0 refl

n∣n : ∀ {n} → n ∣ n
n∣n = ∣-refl

n|m*n : ∀ m {n} → n ∣ m * n
n|m*n m = divides m refl

0∣⇒≡0 : ∀ {n} → 0 ∣ n → n ≡ 0
0∣⇒≡0 {n} 0∣n = ∣-antisym (n ∣0) 0∣n

∣1⇒≡1 : ∀ {n} → n ∣ 1 → n ≡ 1
∣1⇒≡1 {n} n∣1 = ∣-antisym n∣1 (1∣ n)

------------------------------------------------------------------------
-- Operators and divisibility

∣m∣n⇒∣m+n : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m + n
∣m∣n⇒∣m+n (divides p refl) (divides q refl) =
  divides (p + q) (sym (*-distribʳ-+ _ p q))

∣m+n|m⇒|n : ∀ {i m n} → i ∣ m + n → i ∣ m → i ∣ n
∣m+n|m⇒|n {i} {m} {n} (divides p m+n≡p*i) (divides q m≡q*i) =
  divides (p ∸ q) (begin
    n             ≡⟨ sym (m+n∸n≡m n m) ⟩
    n + m ∸ m     ≡⟨ cong (_∸ m) (+-comm n m) ⟩
    m + n ∸ m     ≡⟨ cong₂ _∸_ m+n≡p*i m≡q*i ⟩
    p * i ∸ q * i ≡⟨ sym (*-distribʳ-∸ i p q) ⟩
    (p ∸ q) * i   ∎)
  where open PropEq.≡-Reasoning

∣m∸n∣n⇒∣m : ∀ i {m n} → n ≤ m → i ∣ m ∸ n → i ∣ n → i ∣ m
∣m∸n∣n⇒∣m i {m} {n} n≤m (divides p m∸n≡p*i) (divides q n≡q*o) =
  divides (p + q) (begin
    m             ≡⟨ sym (m+n∸m≡n n≤m) ⟩
    n + (m ∸ n)   ≡⟨ +-comm n (m ∸ n) ⟩
    m ∸ n + n     ≡⟨ cong₂ _+_ m∸n≡p*i n≡q*o ⟩
    p * i + q * i ≡⟨ sym (*-distribʳ-+ i p q)  ⟩
    (p + q) * i   ∎)
  where open PropEq.≡-Reasoning

*-cong : ∀ {i j} k → i ∣ j → k * i ∣ k * j
*-cong {i} {j} k (divides q j≡q*i) = divides q (begin
  k * j        ≡⟨ cong (_*_ k) j≡q*i ⟩
  k * (q * i)  ≡⟨ sym (*-assoc k q i) ⟩
  (k * q) * i  ≡⟨ cong (_* i) (*-comm k q) ⟩
  (q * k) * i  ≡⟨ *-assoc q k i ⟩
  q * (k * i)  ∎)
  where open PropEq.≡-Reasoning

/-cong : ∀ {i j} k → suc k * i ∣ suc k * j → i ∣ j
/-cong {i} {j} k (divides q eq) =
  divides q (*-cancelʳ-≡ j (q * i) (begin
    j * (suc k)        ≡⟨ *-comm j (suc k) ⟩
    (suc k) * j        ≡⟨ eq ⟩
    q * ((suc k) * i)  ≡⟨ cong (q *_) (*-comm (suc k) i) ⟩
    q * (i * (suc k))  ≡⟨ sym (*-assoc q i (suc k)) ⟩
    (q * i) * (suc k)  ∎))
  where open PropEq.≡-Reasoning

-- If the remainder after division is non-zero, then the divisor does
-- not divide the dividend.

nonZeroDivisor-lemma
  : ∀ m q (r : Fin (1 + m)) → toℕ r ≢ 0 →
    1 + m ∤ toℕ r + q * (1 + m)
nonZeroDivisor-lemma m zero r r≢zero (divides zero eq) = r≢zero $ begin
  toℕ r      ≡⟨ sym (*-identityˡ (toℕ r)) ⟩
  1 * toℕ r  ≡⟨ eq ⟩
  0          ∎
  where open PropEq.≡-Reasoning
nonZeroDivisor-lemma m zero r r≢zero (divides (suc q) eq) =
  ¬i+1+j≤i m $ begin
    m + suc (q * suc m) ≡⟨ +-suc m (q * suc m) ⟩
    suc (m + q * suc m) ≡⟨ sym eq ⟩
    1 * toℕ r           ≡⟨ *-identityˡ (toℕ r) ⟩
    toℕ r               ≤⟨ ≤-pred $ FP.bounded r ⟩
    m                   ∎
  where open ≤-Reasoning
nonZeroDivisor-lemma m (suc q) r r≢zero d =
  nonZeroDivisor-lemma m q r r≢zero (∣m+n|m⇒|n d' ∣-refl)
  where
  lem = solve 3 (λ m r q → r :+ (m :+ q)  :=  m :+ (r :+ q))
                refl (suc m) (toℕ r) (q * suc m)
  d' = subst (1 + m ∣_) lem d

-- Divisibility is decidable.

infix 4 _∣?_

_∣?_ : Decidable _∣_
zero  ∣? zero                     = yes (0 ∣0)
zero  ∣? suc n                    = no ((λ()) ∘′ 0∣⇒≡0)
suc m ∣? n                        with n divMod suc m
suc m ∣? .(q * suc m)             | result q zero    refl =
  yes $ divides q refl
suc m ∣? .(1 + toℕ r + q * suc m) | result q (suc r) refl =
  no $ nonZeroDivisor-lemma m q (suc r) (λ())

------------------------------------------------------------------------
-- DEPRECATED - please use new names as continuing support for the old
-- names is not guaranteed.

∣-+ = ∣m∣n⇒∣m+n
∣-∸ = ∣m+n|m⇒|n
∣-* = n|m*n
