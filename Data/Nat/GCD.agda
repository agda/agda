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
open import Logic
open import Relation.Binary.PropositionalEquality
open import Data.Fin
open import Data.Vec
open ℕ-semiringSolver
open import Logic.Induction
open import Logic.Induction.Nat
open import Logic.Induction.Lexicographic
open import Data.Function

------------------------------------------------------------------------
-- Boring lemmas

private

  lem₀ = \n k -> let N = var fz; K = var (fs fz) in
                 prove (n ∷ k ∷ [])
                       (N :+ (con 1 :+ K)) (con 1 :+ N :+ K) ≡-refl

  lem₁ : forall i j -> 2 + i ≤′ 2 + j + i
  lem₁ i j = ≤⇒≤′ $ s≤s $ s≤s $ n≤m+n j i

------------------------------------------------------------------------
-- Greatest common divisor

-- Specification of the greatest common divisor (gcd) of two natural
-- numbers.

record GCD (m n gcd : ℕ) : Set where
  field
    -- The GCD is a common divisor.
    commonDivisor : gcd Divides m And n

    -- All common divisors divide the GCD.
    divisible     : forall {d} -> d Divides m And n -> d Divides gcd

isGCD : forall {gcd m n} ->
        gcd Divides m And n ->
        (forall {d} -> d Divides m And n -> d Divides gcd) ->
        GCD m n gcd
isGCD cd div = record
  { commonDivisor = cd
  ; divisible     = div
  }

-- The GCD is the largest common divisor, except if both dividends are
-- zero (in which case all natural numbers are common divisors).

gcd-largest
  : forall {d d' m n} ->
    GCD m n d -> ¬ (m ≡ 0 × n ≡ 0) -> d' Divides m And n -> d' ≤ d
gcd-largest {zero} g mn≢0 _ with GCD.commonDivisor g
gcd-largest {zero} {d'} {m = .(m * 0)} {n = .(n * 0)} g mn≢0 _
  | (divides m ≡-refl , divides n ≡-refl) =
  ⊥-elim {d' ≤ 0} $ mn≢0 (proj₂ CS.zero m , proj₂ CS.zero n)
gcd-largest {suc _} g _ c = divides-≤ (GCD.divisible g c)

-- The GCD is unique.

gcd-unique : forall {d₁ d₂ m n} -> GCD m n d₁ -> GCD m n d₂ -> d₁ ≡ d₂
gcd-unique d₁ d₂ = divides-≡ (GCD.divisible d₂ (GCD.commonDivisor d₁))
                             (GCD.divisible d₁ (GCD.commonDivisor d₂))

-- The GCD relation is "symmetric".

gcd-sym : forall {d m n} -> GCD m n d -> GCD n m d
gcd-sym g = isGCD (swap $ GCD.commonDivisor g) (GCD.divisible g ∘ swap)

private

  ∃GCD = \m n -> ∃ ℕ (GCD m n)

  step₁ : forall {n k} -> ∃GCD n (suc k) -> ∃GCD n (suc (n + k))
  step₁ (exists d g) with GCD.commonDivisor g
  step₁ {n} {k} (exists d g) | (d₁ , d₂) =
    ≡-subst (∃GCD n) (lem₀ n k) $
      exists d (isGCD (d₁ , divides-+ d₁ d₂) div')
    where
    div' : forall {d'} ->
           d' Divides n And (n + suc k) -> d' Divides d
    div' (d₁ , d₂) = GCD.divisible g (d₁ , divides-∸ d₂ d₁)

  ∃gcd-sym : forall {m n} -> ∃GCD m n -> ∃GCD n m
  ∃gcd-sym (exists d g) = exists d (gcd-sym g)

  step₂ : forall {n k} -> ∃GCD (suc k) n -> ∃GCD (suc (n + k)) n
  step₂ = ∃gcd-sym ∘ step₁ ∘ ∃gcd-sym

-- GCD calculated using Euclid's algorithm (except, perhaps, for the
-- "equal" case).

gcd : (m n : ℕ) -> ∃ ℕ (\d -> GCD m n d)
gcd m n = build [ <-rec-builder ⊗ <-rec-builder ] P gcd' (m , n)
  where
  P : ℕ × ℕ -> Set
  P (m , n) = ∃GCD m n

  res₁ = \n -> exists n       (isGCD (n divides-0          , divides-refl n      ) proj₂)
  res₂ = \m -> exists (suc m) (isGCD (divides-refl (suc m) , suc m divides-0     ) proj₁)
  res₃ = \m -> exists (suc m) (isGCD (divides-refl (suc m) , divides-refl (suc m)) proj₁)

  gcd' : forall p -> (<-Rec ⊗ <-Rec) P p -> P p
  gcd' (zero               , n                 ) rec = res₁ n
  gcd' (suc m              , zero              ) rec = res₂ m
  gcd' (suc m              , suc n             ) rec with compare m n
  gcd' (suc m              , suc .m            ) rec | equal .m     = res₃ m
  gcd' (suc m              , suc .(suc (m + k))) rec | less .m k    =
    step₁ $ proj₁ rec (suc k) (lem₁ k m)          -- gcd (suc m) (suc k)
  gcd' (suc .(suc (n + k)) , suc n             ) rec | greater .n k =
    step₂ $ proj₂ rec (suc k) (lem₁ k n) (suc n)  -- gcd (suc k) (suc n)

-- Another interface to the gcd function, which may sometimes be
-- useful.

data GCD' : ℕ -> ℕ -> Set where
  result : (m n d : ℕ) -> GCD' (m * d) (n * d)

gcd' : (m n : ℕ) -> GCD' m n
gcd' m         n         with gcd m n
gcd' m         n         | exists d g with GCD.commonDivisor g
gcd' .(m' * d) .(n' * d) | exists d g
  | (divides m' ≡-refl , divides n' ≡-refl) = result m' n' d
