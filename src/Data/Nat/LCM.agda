------------------------------------------------------------------------
-- Least common multiple
------------------------------------------------------------------------

module Data.Nat.LCM where

open import Data.Nat
import Data.Nat.Properties as NatProp
open NatProp.SemiringSolver
open import Data.Nat.GCD
open import Data.Nat.Divisibility as Div
open import Data.Nat.Coprimality as Coprime
open import Data.Product
open import Data.Function
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; inspect; _with-≡_)
open import Algebra
open import Relation.Binary
private
  module P  = Poset Div.poset
  module CS = CommutativeSemiring NatProp.commutativeSemiring

------------------------------------------------------------------------
-- Least common multiple (lcm).

module LCM where

  -- Specification of the least common multiple (lcm) of two natural
  -- numbers.

  record LCM (i j lcm : ℕ) : Set where
    field
      -- The lcm is a common multiple.
      commonMultiple : i ∣ lcm × j ∣ lcm

      -- The lcm divides all common multiples, i.e. the lcm is the least
      -- common multiple according to the partial order _∣_.
      least : ∀ {m} → i ∣ m × j ∣ m → lcm ∣ m

  open LCM public

  -- The lcm is unique.

  unique : ∀ {d₁ d₂ m n} → LCM m n d₁ → LCM m n d₂ → d₁ ≡ d₂
  unique d₁ d₂ = P.antisym (LCM.least d₁ (LCM.commonMultiple d₂))
                           (LCM.least d₂ (LCM.commonMultiple d₁))

open LCM public using (LCM)

------------------------------------------------------------------------
-- Calculating the lcm

private
  lem₁ = solve 3 (λ a b c → a :* b :* c  :=  b :* (a :* c)) refl
  lem₂ = solve 3 (λ a b c → a :* b :* c  :=  a :* (b :* c)) refl

  -- If these lemmas are inlined, then type checking takes a lot
  -- longer... (In the development version of Agda from 2009-05-21.)

  mult₁ : ∀ q₁ q₂ d → q₁ * d ∣ q₁ * q₂ * d
  mult₁ q₁ q₂ d = divides q₂ (lem₁ q₁ q₂ d)

  mult₂ : ∀ q₁ q₂ d → q₂ * d ∣ q₁ * q₂ * d
  mult₂ q₁ q₂ d = divides q₁ (lem₂ q₁ q₂ d)

-- The lcm can be calculated from the gcd.

lcm : (i j : ℕ) → ∃ λ d → LCM i j d
lcm i j with gcd′ i j
lcm .(q₁ * d) .(q₂ * d) | (d , gcd-* q₁ q₂ q₁-q₂-coprime) =
  ( q₁ * q₂ * d
  , record { commonMultiple = (mult₁ q₁ q₂ d , mult₂ q₁ q₂ d)
           ; least          = least
           }
  )
  where
  least : ∀ {m} → q₁ * d ∣ m × q₂ * d ∣ m → q₁ * q₂ * d ∣ m
  least div with d
  least (divides q₃ refl , _) | zero = begin
    q₁ * q₂ * 0    ∣⟨ (q₁ * q₂ * 0) ∣0 ⟩
    0              ≡⟨ solve 2 (λ a b → con 0  :=  a :* (b :* con 0))
                              refl q₃ q₁ ⟩
    q₃ * (q₁ * 0)  ∎
    where open ∣-Reasoning
  least {m} (divides q₃ eq₃ , divides q₄ eq₄) | suc d =
    q₁q₂d′∣m q₂∣q₃
    where
    open PropEq.≡-Reasoning
    d′ = suc d

    q₂∣q₃ : q₂ ∣ q₃
    q₂∣q₃ = coprime-divisor (Coprime.sym q₁-q₂-coprime)
              (divides q₄ $ NatProp.cancel-*-right _ _ (begin
                 q₁ * q₃ * d′    ≡⟨ lem₁ q₁ q₃ d′ ⟩
                 q₃ * (q₁ * d′)  ≡⟨ PropEq.sym eq₃ ⟩
                 m               ≡⟨ eq₄ ⟩
                 q₄ * (q₂ * d′)  ≡⟨ PropEq.sym (lem₂ q₄ q₂ d′) ⟩
                 q₄ *  q₂ * d′   ∎))

    q₁q₂d′∣m : q₂ ∣ q₃ → q₁ * q₂ * d′ ∣ m
    q₁q₂d′∣m q₂∣q₃             with q₃      | eq₃
    q₁q₂d′∣m (divides q₅ refl) | .(q₅ * q₂) | eq₃′ =
      divides q₅ (begin
        m                    ≡⟨ eq₃′ ⟩
        q₅ * q₂ * (q₁ * d′)  ≡⟨ solve 4 (λ q₁ q₂ q₅ d′ → q₅ :* q₂ :* (q₁ :* d′)
                                                     :=  q₅ :* (q₁ :* q₂ :* d′))
                                        refl q₁ q₂ q₅ d′ ⟩
        q₅ * (q₁ * q₂ * d′)  ∎)

------------------------------------------------------------------------
-- Properties

-- The product of the gcd and the lcm is the product of the two
-- numbers.

gcd*lcm : ∀ {i j d m} → GCD i j d → LCM i j m → i * j ≡ d * m
gcd*lcm  {i}        {j}       {d}  {m}               g l with LCM.unique l (proj₂ (lcm i j))
gcd*lcm  {i}        {j}       {d} .{proj₁ (lcm i j)} g l | refl with gcd′ i j
gcd*lcm .{q₁ * d′} .{q₂ * d′} {d} .{q₁ * q₂ * d′}    g l | refl | (d′ , gcd-* q₁ q₂ q₁-q₂-coprime)
                                                           with GCD.unique g
                                                                  (gcd′-gcd (gcd-* q₁ q₂ q₁-q₂-coprime))
gcd*lcm .{q₁ * d}  .{q₂ * d}  {d} .{q₁ * q₂ * d}     g l | refl | (.d , gcd-* q₁ q₂ q₁-q₂-coprime) | refl =
  solve 3 (λ q₁ q₂ d → q₁ :* d :* (q₂ :* d)
                   :=  d :* (q₁ :* q₂ :* d))
          refl q₁ q₂ d
