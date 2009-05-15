------------------------------------------------------------------------
-- Greatest common divisor
------------------------------------------------------------------------

module Data.Nat.GCD where

open import Data.Nat
open import Data.Nat.Divisibility as Div
open import Relation.Binary
private module P = Poset Div.poset
open import Data.Product
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Induction
open import Induction.Nat
open import Induction.Lexicographic
open import Data.Function
open import Data.Nat.GCD.Lemmas

------------------------------------------------------------------------
-- Greatest common divisor

module GCD where

  -- Specification of the greatest common divisor (gcd) of two natural
  -- numbers.

  record GCD (m n gcd : ℕ) : Set where
    field
      -- The gcd is a common divisor.
      commonDivisor : gcd ∣ m × gcd ∣ n

      -- All common divisors divide the gcd, i.e. the gcd is the
      -- greatest common divisor according to the partial order _∣_.
      greatest : ∀ {d} → d ∣ m × d ∣ n → d ∣ gcd

  open GCD public

  is : ∀ {gcd m n} →
       gcd ∣ m × gcd ∣ n →
       (∀ {d} → d ∣ m × d ∣ n → d ∣ gcd) →
       GCD m n gcd
  is cd div = record
    { commonDivisor = cd
    ; greatest      = div
    }

  -- The gcd is unique.

  unique : ∀ {d₁ d₂ m n} → GCD m n d₁ → GCD m n d₂ → d₁ ≡ d₂
  unique d₁ d₂ = P.antisym (GCD.greatest d₂ (GCD.commonDivisor d₁))
                           (GCD.greatest d₁ (GCD.commonDivisor d₂))

  -- The gcd relation is "symmetric".

  sym : ∀ {d m n} → GCD m n d → GCD n m d
  sym g = is (swap $ GCD.commonDivisor g) (GCD.greatest g ∘ swap)

  -- The gcd relation is "reflexive".

  refl : ∀ {n} → GCD n n n
  refl = is (P.refl , P.refl) proj₁

  -- The GCD of 0 and n is n.

  base : ∀ {n} → GCD 0 n n
  base {n} = is (n ∣0 , P.refl) proj₂

  -- If d is the gcd of n and k, then it is also the gcd of n and
  -- n + k.

  step : ∀ {n k d} → GCD n k d → GCD n (n + k) d
  step g with GCD.commonDivisor g
  step {n} {k} {d} g | (d₁ , d₂) = is (d₁ , ∣-+ d₁ d₂) greatest′
    where
    greatest′ : ∀ {d′} → d′ ∣ n × d′ ∣ n + k → d′ ∣ d
    greatest′ (d₁ , d₂) = GCD.greatest g (d₁ , ∣-∸ d₂ d₁)

open GCD public using (GCD)

------------------------------------------------------------------------
-- Calculating the gcd

-- The calculation also proves Bézout's lemma.

module Bézout where

  -- If m and n have greatest common divisor d, then one of the
  -- following two equations is satisfied, for some numbers x and y.
  -- The proof is "lemma" below (Bézout's lemma).
  --
  -- (If this identity was stated using integers instead of natural
  -- numbers, then it would not be necessary to have two equations.)

  data Identity (d m n : ℕ) : Set where
    +- : (x y : ℕ) (eq : d + y * n ≡ x * m) → Identity d m n
    -+ : (x y : ℕ) (eq : d + x * m ≡ y * n) → Identity d m n

  module Identity where

    -- Various properties about Identity.

    sym : ∀ {d} → Symmetric (Identity d)
    sym (+- x y eq) = -+ y x eq
    sym (-+ x y eq) = +- y x eq

    refl : ∀ {d} → Identity d d d
    refl = -+ 0 1 PropEq.refl

    base : ∀ {d} → Identity d 0 d
    base = -+ 0 1 PropEq.refl

    private
      infixl 7 _⊕_

      _⊕_ : ℕ → ℕ → ℕ
      m ⊕ n = 1 + m + n

    step : ∀ {d n k} → Identity d n k → Identity d n (n + k)
    step {d}     (+-  x  y       eq) with compare x y
    step {d}     (+- .x .x       eq) | equal x     = +- (2 * x)     x       (lem₂ d x   eq)
    step {d}     (+- .x .(x ⊕ i) eq) | less x i    = +- (2 * x ⊕ i) (x ⊕ i) (lem₃ d x   eq)
    step {d} {n} (+- .(y ⊕ i) .y eq) | greater y i = +- (2 * y ⊕ i) y       (lem₄ d y n eq)
    step {d}     (-+  x  y       eq) with compare x y
    step {d}     (-+ .x .x       eq) | equal x     = -+ (2 * x)     x       (lem₅ d x   eq)
    step {d}     (-+ .x .(x ⊕ i) eq) | less x i    = -+ (2 * x ⊕ i) (x ⊕ i) (lem₆ d x   eq)
    step {d} {n} (-+ .(y ⊕ i) .y eq) | greater y i = -+ (2 * y ⊕ i) y       (lem₇ d y n eq)

  -- This type packs up the gcd, the proof that it is a gcd, and the
  -- proof that it satisfies Bézout's identity.

  data Lemma (m n : ℕ) : Set where
    result : (d : ℕ) (g : GCD m n d) (b : Identity d m n) → Lemma m n

  module Lemma where

    -- Various properties about Lemma.

    sym : Symmetric Lemma
    sym (result d g b) = result d (GCD.sym g) (Identity.sym b)

    base : ∀ d → Lemma 0 d
    base d = result d GCD.base Identity.base

    refl : ∀ d → Lemma d d
    refl d = result d GCD.refl Identity.refl

    stepˡ : ∀ {n k} → Lemma n (suc k) → Lemma n (suc (n + k))
    stepˡ {n} {k} (result d g b) =
      PropEq.subst (Lemma n) (lem₀ n k) $
        result d (GCD.step g) (Identity.step b)

    stepʳ : ∀ {n k} → Lemma (suc k) n → Lemma (suc (n + k)) n
    stepʳ = sym ∘ stepˡ ∘ sym

  -- Bézout's lemma proved using some variant of the extended
  -- Euclidean algorithm.

  lemma : (m n : ℕ) → Lemma m n
  lemma m n = build [ <-rec-builder ⊗ <-rec-builder ] P gcd (m , n)
    where
    P : ℕ × ℕ → Set
    P (m , n) = Lemma m n

    gcd : ∀ p → (<-Rec ⊗ <-Rec) P p → P p
    gcd (zero  , n                 ) rec = Lemma.base n
    gcd (suc m , zero              ) rec = Lemma.sym (Lemma.base (suc m))
    gcd (suc m , suc n             ) rec with compare m n
    gcd (suc m , suc .m            ) rec | equal .m     = Lemma.refl (suc m)
    gcd (suc m , suc .(suc (m + k))) rec | less .m k    =
                      -- "gcd (suc m) (suc k)"
      Lemma.stepˡ $ proj₁ rec (suc k) (lem₁ k m)
    gcd (suc .(suc (n + k)) , suc n) rec | greater .n k =
                      -- "gcd (suc k) (suc n)"
      Lemma.stepʳ $ proj₂ rec (suc k) (lem₁ k n) (suc n)

  -- Bézout's identity can be recovered from the GCD.

  identity : ∀ {m n d} → GCD m n d → Identity d m n
  identity {m} {n} g with lemma m n
  identity g | result d g′ b with GCD.unique g g′
  identity g | result d g′ b | PropEq.refl = b

-- Calculates the gcd of the arguments.

gcd : (m n : ℕ) → ∃ λ d → GCD m n d
gcd m n with Bézout.lemma m n
gcd m n | Bézout.result d g _ = (d , g)
