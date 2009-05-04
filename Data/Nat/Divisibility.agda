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
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; _≢_; refl; sym; cong; subst)
open import Data.Function

-- m Divides n is inhabited iff m divides n. Some sources, like Hardy
-- and Wright's "An Introduction to the Theory of Numbers", require m
-- to be non-zero. However, some things become a bit nicer if m is
-- allowed to be zero. For instance, _Divides_ becomes a partial
-- order, and the gcd of 0 and 0 becomes defined.

data _Divides_ : ℕ → ℕ → Set where
  divides : {m n : ℕ} (q : ℕ) (eq : n ≡ q * m) → m Divides n

-- Extracts the quotient.

quotient : ∀ {m n} → m Divides n → ℕ
quotient (divides q _) = q

-- d Divides m And n means that d is a common divisor of m and n.

_Divides_And_ : (d m n : ℕ) → Set
d Divides m And n = d Divides m × d Divides n

-- If m divides n, and n is positive, then m ≤ n.

divides-≤ : ∀ {m n} → m Divides suc n → m ≤ suc n
divides-≤         (divides zero    ())
divides-≤ {m} {n} (divides (suc q) eq) = begin
  m
    ≤⟨ NatProp.m≤m+n m (q * m) ⟩
  suc q * m
    ≡⟨ sym eq ⟩
  suc n
    ∎
  where open ≤-Reasoning

-- _Divides_ is a partial order.

poset : Poset
poset = record
  { carrier        = ℕ
  ; _≈_            = _≡_
  ; _≤_            = _Divides_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = PropEq.isEquivalence
      ; reflexive     = reflexive
      ; trans         = trans
      ; ≈-resp-∼      = PropEq.resp _Divides_
      }
    ; antisym = antisym
    }
  }
  where
  module P = Poset Nat.poset
  open PropEq.≡-Reasoning

  reflexive : _≡_ ⇒ _Divides_
  reflexive {n} refl = divides 1 (sym $ proj₁ CS.*-identity n)

  antisym : Antisymmetric _≡_ _Divides_
  antisym (divides {n = zero} q₁ eq₁) (divides {n = n₂} q₂ eq₂) = begin
    n₂      ≡⟨ eq₂ ⟩
    q₂ * 0  ≡⟨ CS.*-comm q₂ 0 ⟩
    0       ∎
  antisym (divides {n = n₁} q₁ eq₁) (divides {n = zero} q₂ eq₂) = begin
    0       ≡⟨ CS.*-comm 0 q₁ ⟩
    q₁ * 0  ≡⟨ sym eq₁ ⟩
    n₁      ∎
  antisym (divides {n = suc n₁} q₁ eq₁) (divides {n = suc n₂} q₂ eq₂) =
    P.antisym (divides-≤ (divides q₁ eq₁)) (divides-≤ (divides q₂ eq₂))

  trans : Transitive _Divides_
  trans (divides q₁ refl) (divides q₂ refl) =
    divides (q₂ * q₁) (sym (CS.*-assoc q₂ q₁ _))

-- 1 divides everything.

1-divides_ : ∀ n → 1 Divides n
1-divides n = divides n (sym $ proj₂ CS.*-identity n)

-- Everything divides 0.

_divides-0 : ∀ n → n Divides 0
n divides-0 = divides 0 refl

-- 0 only divides zero.

0-onlyDivides-0 : ∀ {n} → 0 Divides n → n ≡ 0
0-onlyDivides-0 (divides q refl) = CS.*-comm q 0

-- If i divides m and n, then i divides their sum.

divides-+ : ∀ {i m n} → i Divides m → i Divides n → i Divides (m + n)
divides-+ (divides {m = i} q refl) (divides q' refl) =
  divides (q + q') (sym $ proj₂ CS.distrib i q q')

-- If i divides m and n, then i divides their difference.

divides-∸ : ∀ {i m n} → i Divides (m + n) → i Divides m → i Divides n
divides-∸ (divides {m = i} q' eq) (divides q refl) =
  divides (q' ∸ q)
          (sym $ NatProp.im≡jm+n⇒[i∸j]m≡n q' q i _ $ sym eq)

-- If i divides i + n then i divides n.

divides-Δ : ∀ {i n} → i Divides (i + n) → i Divides n
divides-Δ d = divides-∸ d P.refl
  where module P = Poset poset

-- If the remainder after division is non-zero, then the divisor does
-- not divide the dividend.

nonZeroDivisor-lemma
  : ∀ m q (r : Fin (1 + m)) → Fin.toℕ r ≢ 0 →
    ¬ (1 + m) Divides (Fin.toℕ r + q * (1 + m))
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
  nonZeroDivisor-lemma m q r r≢zero (divides-Δ d')
  where
  lem = solve 3 (λ m r q → r :+ (m :+ q)  :=  m :+ (r :+ q))
                refl (suc m) (Fin.toℕ r) (q * suc m)
  d' = subst (λ x → (1 + m) Divides x) lem d

-- Divisibility is decidable.

divisible? : Decidable _Divides_
divisible? zero    zero    = yes (0 divides-0)
divisible? zero    (suc n) = no ((λ ()) ∘′ 0-onlyDivides-0)
divisible? (suc m) n                            with n divMod suc m
divisible? (suc m) .(q * suc m)                 | result q zero    =
  yes $ divides q refl
divisible? (suc m) .(1 + Fin.toℕ r + q * suc m) | result q (suc r) =
  no $ nonZeroDivisor-lemma m q (suc r) (λ())
