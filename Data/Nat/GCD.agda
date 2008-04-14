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

data GCD (m : ℕ) (n : ℕ) : Set where
  result : (gcd : ℕ) ->
           CommonDivisor gcd m n ->
           (forall {d} -> CommonDivisor d m n -> d Divides gcd) ->
           GCD m n

-- Extracts the GCD.

theGCD : forall {m n} -> GCD m n -> ℕ
theGCD (result d _ _) = d

-- The GCD is a common divisor.

gcd-commonDivisor : forall {m n}
                    (g : GCD m n) -> CommonDivisor (theGCD g) m n
gcd-commonDivisor (result _ cd _) = cd

-- All common divisors divide the GCD.

gcd-divisible
  : forall {d m n}
    (g : GCD m n) -> CommonDivisor d m n -> d Divides theGCD g
gcd-divisible (result _ _ div) = div

-- The GCD is the largest common divisor, except if both dividends are
-- zero (in which case all natural numbers are common divisors).

gcd-largest : forall {d m n} (g : GCD m n) ->
              ¬ (m ≡ 0 × n ≡ 0) -> CommonDivisor d m n -> d ≤ theGCD g
gcd-largest {d} (result zero (divides m ≡-refl , divides n ≡-refl) _)
                mn≢0 c =
  ⊥-elim {d ≤ 0} $ mn≢0 (proj₂ CS.zero m , proj₂ CS.zero n)
gcd-largest (result (suc _) _ div) _ c = divides-≤ (div c)

-- The GCD is unique.

gcd-unique : forall {m n} (d₁ d₂ : GCD m n) -> theGCD d₁ ≡ theGCD d₂
gcd-unique d₁ d₂ = divides-≡ (gcd-divisible d₂ (gcd-commonDivisor d₁))
                             (gcd-divisible d₁ (gcd-commonDivisor d₂))

private

  -- The GCD relation is symmetric.

  gcd-sym : forall {m n} -> GCD m n -> GCD n m
  gcd-sym (result d cd div) = result d (swap cd) (div ∘ swap)

  step₁ : forall {n k} -> GCD n (suc k) -> GCD n (suc (n + k))
  step₁ {n} {k} (result d (d₁ , d₂) div) =
    ≡-subst (GCD n) (lem₀ n k) $
      result d (d₁ , divides-+ d₁ d₂) div'
    where
    div' : forall {d'} ->
           CommonDivisor d' n (n + suc k) -> d' Divides d
    div' (d₁ , d₂) = div (d₁ , divides-∸ d₂ d₁)

  step₂ : forall {n k} -> GCD (suc k) n -> GCD (suc (n + k)) n
  step₂ = gcd-sym ∘ step₁ ∘ gcd-sym

-- GCD calculated using Euclid's algorithm (except, perhaps, for the
-- "equal" case).

gcd : (m n : ℕ) -> GCD m n
gcd m n = build [ <-rec-builder ⊗ <-rec-builder ] P gcd' (m , n)
  where
  P : ℕ × ℕ -> Set
  P (m , n) = GCD m n

  res₁ = \n -> result n       (n divides-0          , divides-refl n      ) proj₂
  res₂ = \m -> result (suc m) (divides-refl (suc m) , suc m divides-0     ) proj₁
  res₃ = \m -> result (suc m) (divides-refl (suc m) , divides-refl (suc m)) proj₁

  gcd' : forall p -> (<-Rec ⊗ <-Rec) P p -> P p
  gcd' (zero               , n                 ) rec = res₁ n
  gcd' (suc m              , zero              ) rec = res₂ m
  gcd' (suc m              , suc n             ) rec with compare m n
  gcd' (suc m              , suc .m            ) rec | equal .m     = res₃ m
  gcd' (suc m              , suc .(suc (m + k))) rec | less .m k    =
    step₁ $ proj₁ rec (suc k) (lem₁ k m)          -- gcd (suc m) (suc k)
  gcd' (suc .(suc (n + k)) , suc n             ) rec | greater .n k =
    step₂ $ proj₂ rec (suc k) (lem₁ k n) (suc n)  -- gcd (suc k) (suc n)
