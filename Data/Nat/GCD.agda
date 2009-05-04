------------------------------------------------------------------------
-- Greatest common divisor
------------------------------------------------------------------------

module Data.Nat.GCD where

open import Data.Nat
open import Data.Nat.Divisibility as Div
import Data.Nat.Properties as NatProp
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open NatProp.SemiringSolver
open import Induction
open import Induction.Nat
open import Induction.Lexicographic
open import Data.Function
open import Relation.Binary
private
  module P = Poset Div.poset

------------------------------------------------------------------------
-- Boring lemmas

private

  lem₀ = solve 2 (λ n k → n :+ (con 1 :+ k)  :=  con 1 :+ n :+ k)
                 PropEq.refl

  lem₁ : ∀ i j → 1 + i ≤′ 1 + j + i
  lem₁ i j = NatProp.≤⇒≤′ $ s≤s $ NatProp.n≤m+n j i

------------------------------------------------------------------------
-- Greatest common divisor

-- Specification of the greatest common divisor (gcd) of two natural
-- numbers.

record GCD (m n gcd : ℕ) : Set where
  field
    -- The gcd is a common divisor.
    commonDivisor : gcd Divides m And n

    -- All common divisors divide the gcd, i.e. the gcd is the largest
    -- common divisor according to the partial order _Divides_.
    greatest : ∀ {d} → d Divides m And n → d Divides gcd

isGCD : ∀ {gcd m n} →
        gcd Divides m And n →
        (∀ {d} → d Divides m And n → d Divides gcd) →
        GCD m n gcd
isGCD cd div = record
  { commonDivisor = cd
  ; greatest      = div
  }

-- The gcd is unique.

unique : ∀ {d₁ d₂ m n} → GCD m n d₁ → GCD m n d₂ → d₁ ≡ d₂
unique d₁ d₂ = P.antisym (GCD.greatest d₂ (GCD.commonDivisor d₁))
                         (GCD.greatest d₁ (GCD.commonDivisor d₂))

-- The gcd relation is "symmetric".

sym : ∀ {d m n} → GCD m n d → GCD n m d
sym g = isGCD (swap $ GCD.commonDivisor g) (GCD.greatest g ∘ swap)

-- The gcd relation is "reflexive".

refl : ∀ n → GCD n n n
refl n = isGCD (P.refl , P.refl) proj₁

-- The GCD of 0 and n is n.

gcd-0 : ∀ n → GCD 0 n n
gcd-0 n = isGCD (n divides-0 , P.refl) proj₂

private

  ∃GCD = λ (m n : ℕ) → ∃ (GCD m n)

  step₁ : ∀ {n k} → ∃GCD n (suc k) → ∃GCD n (suc (n + k))
  step₁ (d , g) with GCD.commonDivisor g
  step₁ {n} {k} (d , g) | (d₁ , d₂) =
    PropEq.subst (∃GCD n) (lem₀ n k) $
      (d , isGCD (d₁ , divides-+ d₁ d₂) div')
    where
    div' : ∀ {d'} → d' Divides n And (n + suc k) → d' Divides d
    div' (d₁ , d₂) = GCD.greatest g (d₁ , divides-∸ d₂ d₁)

  step₂ : ∀ {n k} → ∃GCD (suc k) n → ∃GCD (suc (n + k)) n
  step₂ = map id sym ∘ step₁ ∘ map id sym

-- Gcd calculated using (a variant of) Euclid's algorithm. Note that
-- it is the gcd of the successors of the arguments that is
-- calculated.

gcd⁺ : (m n : ℕ) → ∃ λ d → GCD (suc m) (suc n) d
gcd⁺ m n = build [ <-rec-builder ⊗ <-rec-builder ] P gcd' (m , n)
  where
  P : ℕ × ℕ → Set
  P (m , n) = ∃GCD (suc m) (suc n)

  gcd' : ∀ p → (<-Rec ⊗ <-Rec) P p → P p
  gcd' (m , n             ) rec with compare m n
  gcd' (m , .m            ) rec | equal .m     = (suc m , refl (suc m))
                                                         -- gcd⁺ m k
  gcd' (m , .(suc (m + k))) rec | less .m k    = step₁ $ proj₁ rec k (lem₁ k m)
                                                         -- gcd⁺ k n
  gcd' (.(suc (n + k)) , n) rec | greater .n k = step₂ $ proj₂ rec k (lem₁ k n) n

-- Calculates the gcd of the arguments.

gcd : (m n : ℕ) → ∃ λ d → GCD m n d
gcd (suc m) (suc n) = gcd⁺ m n
gcd zero    n       = (n , gcd-0 n)
gcd m       zero    = (m , sym (gcd-0 m))
