------------------------------------------------------------------------
-- Divisibility
------------------------------------------------------------------------

module Data.Nat.Divisibility where

open import Data.Nat as Nat hiding (poset)
open import Data.Nat.DivMod
import Data.Nat.Properties as NatProp
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Props as FP
open NatProp.SemiringSolver
open import Algebra
private
  module CS = CommutativeSemiring NatProp.commutativeSemiring
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PartialOrderReasoning as PartialOrderReasoning
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; subst)
open import Data.Function

-- m ∣ n is inhabited iff m divides n. Some sources, like Hardy and
-- Wright's "An Introduction to the Theory of Numbers", require m to
-- be non-zero. However, some things become a bit nicer if m is
-- allowed to be zero. For instance, _∣_ becomes a partial order, and
-- the gcd of 0 and 0 becomes defined.

infix 4 _∣_

data _∣_ : ℕ → ℕ → Set where
  divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * m) → m ∣ n

-- Extracts the quotient.

quotient : ∀ {m n} → m ∣ n → ℕ
quotient (divides q _) = q

-- If m divides n, and n is positive, then m ≤ n.

∣⇒≤ : ∀ {m n} → m ∣ suc n → m ≤ suc n
∣⇒≤         (divides zero    ())
∣⇒≤ {m} {n} (divides (suc q) eq) = begin
  m          ≤⟨ NatProp.m≤m+n m (q * m) ⟩
  suc q * m  ≡⟨ sym eq ⟩
  suc n      ∎
  where open ≤-Reasoning

-- _∣_ is a partial order.

poset : Poset
poset = record
  { carrier        = ℕ
  ; _≈_            = _≡_
  ; _≤_            = _∣_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive     = reflexive
      ; trans         = trans
      ; ∼-resp-≈      = PropEq.resp₂ _∣_
      }
    ; antisym = antisym
    }
  }
  where
  module P = Poset Nat.poset
  open PropEq.≡-Reasoning

  reflexive : _≡_ ⇒ _∣_
  reflexive {n} refl = divides 1 (sym $ proj₁ CS.*-identity n)

  antisym : Antisymmetric _≡_ _∣_
  antisym (divides {n = zero} q₁ eq₁) (divides {n = n₂} q₂ eq₂) = begin
    n₂      ≡⟨ eq₂ ⟩
    q₂ * 0  ≡⟨ CS.*-comm q₂ 0 ⟩
    0       ∎
  antisym (divides {n = n₁} q₁ eq₁) (divides {n = zero} q₂ eq₂) = begin
    0       ≡⟨ CS.*-comm 0 q₁ ⟩
    q₁ * 0  ≡⟨ sym eq₁ ⟩
    n₁      ∎
  antisym (divides {n = suc n₁} q₁ eq₁) (divides {n = suc n₂} q₂ eq₂) =
    P.antisym (∣⇒≤ (divides q₁ eq₁)) (∣⇒≤ (divides q₂ eq₂))

  trans : Transitive _∣_
  trans (divides q₁ refl) (divides q₂ refl) =
    divides (q₂ * q₁) (sym (CS.*-assoc q₂ q₁ _))

module ∣-Reasoning = PartialOrderReasoning poset
  renaming (_≤⟨_⟩_ to _∣⟨_⟩_; _≈⟨_⟩_ to _≡⟨_⟩_)

private module P = Poset poset

-- 1 divides everything.

1∣_ : ∀ n → 1 ∣ n
1∣ n = divides n (sym $ proj₂ CS.*-identity n)

-- Everything divides 0.

_∣0 : ∀ n → n ∣ 0
n ∣0 = divides 0 refl

-- 0 only divides 0.

0∣0 : ∀ {n} → 0 ∣ n → n ≡ 0
0∣0 {n} 0∣n = P.antisym (n ∣0) 0∣n

-- Only 1 divides 1.

1∣1 : ∀ {n} → n ∣ 1 → n ≡ 1
1∣1 {n} n∣1 = P.antisym n∣1 (1∣ n)

-- If i divides m and n, then i divides their sum.

∣-+ : ∀ {i m n} → i ∣ m → i ∣ n → i ∣ m + n
∣-+ (divides {m = i} q refl) (divides q' refl) =
  divides (q + q') (sym $ proj₂ CS.distrib i q q')

-- If i divides m and n, then i divides their difference.

∣-∸ : ∀ {i m n} → i ∣ m + n → i ∣ m → i ∣ n
∣-∸ (divides {m = i} q' eq) (divides q refl) =
  divides (q' ∸ q)
          (sym $ NatProp.im≡jm+n⇒[i∸j]m≡n q' q i _ $ sym eq)

-- A simple lemma: n divides kn.

∣-* : ∀ k {n} → n ∣ k * n
∣-* k = divides k refl

-- If i divides j, then ki divides kj.

*-cong : ∀ {i j} k → i ∣ j → k * i ∣ k * j
*-cong {i} {j} k (divides q eq) = divides q lemma
  where
  open PropEq.≡-Reasoning
  lemma = begin
    k * j        ≡⟨ cong (_*_ k) eq ⟩
    k * (q * i)  ≡⟨ solve 3 (λ k q i → k :* (q :* i)
                                   :=  q :* (k :* i))
                            refl k q i ⟩
    q * (k * i)  ∎

-- If ki divides kj, and k is positive, then i divides j.

/-cong : ∀ {i j} k → suc k * i ∣ suc k * j → i ∣ j
/-cong {i} {j} k (divides q eq) = divides q lemma
  where
  open PropEq.≡-Reasoning
  k′    = suc k
  lemma = NatProp.cancel-*-right j (q * i) (begin
    j * k′        ≡⟨ CS.*-comm j k′ ⟩
    k′ * j        ≡⟨ eq ⟩
    q * (k′ * i)  ≡⟨ solve 3 (λ q k i → q :* (k :* i)
                                    :=  q :* i :* k)
                             refl q k′ i ⟩
    q * i * k′    ∎)

-- If the remainder after division is non-zero, then the divisor does
-- not divide the dividend.

nonZeroDivisor-lemma
  : ∀ m q (r : Fin (1 + m)) → Fin.toℕ r ≢ 0 →
    ¬ (1 + m) ∣ (Fin.toℕ r + q * (1 + m))
nonZeroDivisor-lemma m zero r r≢zero (divides zero eq) = r≢zero $ begin
  Fin.toℕ r
    ≡⟨ sym $ proj₁ CS.*-identity (Fin.toℕ r) ⟩
  1 * Fin.toℕ r
    ≡⟨ eq ⟩
  0
    ∎
  where open PropEq.≡-Reasoning
nonZeroDivisor-lemma m zero r r≢zero (divides (suc q) eq) =
  NatProp.¬i+1+j≤i m $ begin
    m + suc (q * suc m)
      ≡⟨ solve 2 (λ m q → m :+ (con 1 :+ q)  :=  con 1 :+ m :+ q)
                 refl m (q * suc m) ⟩
    suc (m + q * suc m)
      ≡⟨ sym eq ⟩
    1 * Fin.toℕ r
      ≡⟨ proj₁ CS.*-identity (Fin.toℕ r) ⟩
    Fin.toℕ r
      ≤⟨ ≤-pred $ FP.bounded r ⟩
    m
      ∎
  where open ≤-Reasoning
nonZeroDivisor-lemma m (suc q) r r≢zero d =
  nonZeroDivisor-lemma m q r r≢zero (∣-∸ d' P.refl)
  where
  lem = solve 3 (λ m r q → r :+ (m :+ q)  :=  m :+ (r :+ q))
                refl (suc m) (Fin.toℕ r) (q * suc m)
  d' = subst (λ x → (1 + m) ∣ x) lem d

-- Divisibility is decidable.

_∣?_ : Decidable _∣_
zero  ∣? zero                         = yes (0 ∣0)
zero  ∣? suc n                        = no ((λ ()) ∘′ 0∣0)
suc m ∣? n                            with n divMod suc m
suc m ∣? .(q * suc m)                 | result q zero    =
  yes $ divides q refl
suc m ∣? .(1 + Fin.toℕ r + q * suc m) | result q (suc r) =
  no $ nonZeroDivisor-lemma m q (suc r) (λ())
