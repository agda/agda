------------------------------------------------------------------------
-- Greatest common divisor
------------------------------------------------------------------------

module Data.Nat.GCD where

open import Data.Nat
open import Data.Nat.Divisibility
open import Data.Nat.Properties
open import Algebra
private
  module CS = CommutativeSemiring ℕ-commutativeSemiring
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Vec
open ℕ-semiringSolver
open import Induction
open import Induction.Nat
open import Induction.Lexicographic
open import Data.Function
open import Data.Empty
open import Relation.Nullary

------------------------------------------------------------------------
-- Boring lemmas

private

  lem₀ = \n k -> let N = var zero; K = var (suc zero) in
                 prove (n ∷ k ∷ [])
                       (N :+ (con 1 :+ K)) (con 1 :+ N :+ K) ≡-refl

  lem₁ : forall i j -> 1 + i ≤′ 1 + j + i
  lem₁ i j = ≤⇒≤′ $ s≤s $ n≤m+n j i

  lem₂ : forall {n} -> ¬ 1 + n ≤ n
  lem₂ (s≤s 1+n≤n) = lem₂ 1+n≤n

------------------------------------------------------------------------
-- Greatest common divisor

-- Specification of the greatest common divisor (gcd) of two natural
-- numbers.

record GCD (m n gcd : ℕ) : Set where
  field
    -- The gcd is a common divisor.
    commonDivisor : gcd Divides m And n

    -- All common divisors divide the gcd.
    divisible     : forall {d} -> d Divides m And n -> d Divides gcd

isGCD : forall {gcd m n} ->
        gcd Divides m And n ->
        (forall {d} -> d Divides m And n -> d Divides gcd) ->
        GCD m n gcd
isGCD cd div = record
  { commonDivisor = cd
  ; divisible     = div
  }

-- The gcd is the largest common divisor.

gcd-largest : forall {d d' m n} ->
              GCD m n d -> d' Divides m And n -> d' ≤ d
gcd-largest {zero}  g _ = ⊥-elim {_ ≤ 0} $ 0-doesNotDivide $
                            proj₁ (GCD.commonDivisor g)
gcd-largest {suc _} g c = divides-≤ (GCD.divisible g c)

-- The gcd is unique.

gcd-unique : forall {d₁ d₂ m n} -> GCD m n d₁ -> GCD m n d₂ -> d₁ ≡ d₂
gcd-unique d₁ d₂ = divides-≡ (GCD.divisible d₂ (GCD.commonDivisor d₁))
                             (GCD.divisible d₁ (GCD.commonDivisor d₂))

-- The gcd relation is "symmetric".

gcd-sym : forall {d m n} -> GCD m n d -> GCD n m d
gcd-sym g = isGCD (swap $ GCD.commonDivisor g) (GCD.divisible g ∘ swap)

-- The gcd relation is "reflexive" (for positive numbers).

gcd-refl : forall n -> let m = suc n in GCD m m m
gcd-refl n = isGCD (divides-refl n , divides-refl n) proj₁

-- 0 and 0 have no gcd.

no-GCD-for-0-0 : ∄ \d -> GCD 0 0 d
no-GCD-for-0-0 (0 , g) = 0-doesNotDivide $ proj₁ $ GCD.commonDivisor g
no-GCD-for-0-0 (suc n , g) = lem₂ 1+d≤d
  where
  d = suc n
  1+d|0 = d +1-divides-0
  1+d|d = GCD.divisible g (1+d|0 , 1+d|0)
  1+d≤d = divides-≤ 1+d|d

-- The GCD of 0 and n, for positive n, is n.

gcd-0-pos : forall n -> GCD 0 (suc n) (suc n)
gcd-0-pos n = isGCD (n +1-divides-0 , divides-refl n) proj₂

private

  ∃GCD = \m n -> ∃ (GCD m n)

  step₁ : forall {n k} -> ∃GCD n (suc k) -> ∃GCD n (suc (n + k))
  step₁ (d , g) with GCD.commonDivisor g
  step₁ {n} {k} (d , g) | (d₁ , d₂) =
    ≡-subst (∃GCD n) (lem₀ n k) $
      (d , isGCD (d₁ , divides-+ d₁ d₂) div')
    where
    div' : forall {d'} ->
           d' Divides n And (n + suc k) -> d' Divides d
    div' (d₁ , d₂) = GCD.divisible g (d₁ , divides-∸ d₂ d₁)

  step₂ : forall {n k} -> ∃GCD (suc k) n -> ∃GCD (suc (n + k)) n
  step₂ = map-Σ₂ gcd-sym ∘ step₁ ∘ map-Σ₂ gcd-sym

-- Gcd calculated using (a variant of) Euclid's algorithm. Note that
-- it is the gcd of the successors of the arguments that is
-- calculated.

gcd⁺ : (m n : ℕ) -> ∃ \d -> GCD (suc m) (suc n) d
gcd⁺ m n = build [ <-rec-builder ⊗ <-rec-builder ] P gcd' (m , n)
  where
  P : ℕ × ℕ -> Set
  P (m , n) = ∃GCD (suc m) (suc n)

  gcd' : forall p -> (<-Rec ⊗ <-Rec) P p -> P p
  gcd' (m , n             ) rec with compare m n
  gcd' (m , .m            ) rec | equal .m     = (suc m , gcd-refl m)
                                                         -- gcd⁺ m k
  gcd' (m , .(suc (m + k))) rec | less .m k    = step₁ $ proj₁ rec k (lem₁ k m)
                                                         -- gcd⁺ k n
  gcd' (.(suc (n + k)) , n) rec | greater .n k = step₂ $ proj₂ rec k (lem₁ k n) n

-- Calculates the gcd of the arguments, of which at least one must be
-- positive.

gcd : (m : ℕ) (n : ℕ) {mn≢0 : False ((m * n) ≟ 0)} ->
      ∃ \d -> GCD m n d
gcd (suc m) (suc n) = gcd⁺ m n
gcd (suc m) zero    = (suc m , gcd-sym (gcd-0-pos m))
gcd zero    (suc n) = (suc n , gcd-0-pos n)
gcd zero    zero {mn≢0 = ()}
